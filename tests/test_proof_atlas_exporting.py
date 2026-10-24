"""Sharded extraction publication tests; no Lean processes are started."""

from contextlib import ExitStack
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

from tools.proof_atlas import exporting


class ExportingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "project"
        self.root.mkdir()
        (self.root / "lean-toolchain").write_text("lean-test\n", encoding="utf-8")
        self.data = Path(self.temp.name) / "index"
        self.data.mkdir()
        self.output = self.data / "export.jsonl"
        self.args = SimpleNamespace(project_root=self.root, data_dir=self.data)
        self.manifest = {"sources": {"OTSelector.lean": "source"}, "content_hash": "source-snapshot",
                         "project_root": str(self.root), "toolchain": "lean-test"}
        context = ExitStack()
        self.addCleanup(context.close)
        self.manifest_mock = context.enter_context(patch.object(exporting, "source_manifest", return_value=self.manifest))
        self.native = context.enter_context(patch.object(exporting, "native_extractor", return_value=self.data / "binary"))
        self.run = context.enter_context(patch.object(exporting.subprocess, "run", side_effect=self.fake_run))
        self.records_hook = None

    def fake_run(self, command, **kwargs):
        output = Path(command[command.index("--output") + 1])
        count = int(command[command.index("--shard-count") + 1])
        index = int(command[command.index("--shard-index") + 1])
        name = f"Demo.decl{index}"
        records = [
            {"record_type": "manifest", "schema_version": 1, "shard_count": count,
             "shard_index": index, "lean_version": "test", "imports": ["OTSelector"],
             "partition_rule": "name_hash", "ast_encoding": "expr_dag_v1", "proof_budget": 2000},
            {"record_type": "declaration", "name": name, "module": "Demo", "external": False},
            {"record_type": "triad", "declaration": name, "target_text": "True"},
            {"record_type": "declaration", "name": "External.shared", "module": "Mathlib", "external": True},
            {"record_type": "summary", "declarations": 1, "triads": 1, "failures": 0,
             "external_references": 1, "owned_count": 1, "project_owned_count": count,
             "complete": True, "scope_complete": True, "full_corpus": False,
             "shard_count": count, "shard_index": index}]
        if self.records_hook:
            self.records_hook(records, index)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text("".join(json.dumps(record) + "\n" for record in records), encoding="utf-8")
        return subprocess.CompletedProcess(command, 0)

    def export(self, module="OTSelector", jobs=2):
        return exporting.export_corpus(self.args, self.output, module, "public", jobs=jobs)

    def test_deterministic_merge_deduplicates_stubs_and_reuses_source_bound_parts(self):
        first = self.export()
        records = [json.loads(line) for line in self.output.read_text().splitlines()]
        self.assertEqual(sum(record["record_type"] == "manifest" for record in records), 1)
        self.assertEqual(sum(record["record_type"] == "summary" for record in records), 1)
        own = [record["name"] for record in records if record["record_type"] == "declaration"
               and not record.get("external")]
        self.assertEqual(own, ["Demo.decl0", "Demo.decl1"])
        self.assertEqual(records[-1]["external_references"], 1)
        self.assertTrue(records[-1]["full_corpus"])
        self.assertEqual(records[-1]["export_scope"], "full_project")
        original = self.output.read_bytes()
        self.export()
        self.assertEqual(self.run.call_count, 2)
        self.assertEqual(self.output.read_bytes(), original)
        status = json.loads((self.data / "export-status.json").read_text())
        self.assertEqual(status["state"], "complete")
        self.assertEqual(status["part_directory"], first["part_directory"])
        for index in range(2):
            part_status = Path(first["part_directory"]) / f"part-{index:05d}.status.json"
            self.assertTrue(json.loads(part_status.read_text())["reused"])
        self.assertFalse((self.data / "atlas.sqlite3").exists())

    def test_duplicate_owned_declaration_rejects_merge_and_preserves_old_output(self):
        self.output.write_text("previous complete export", encoding="utf-8")
        self.records_hook = lambda records, index: records[1].update(name="Demo.duplicate")
        with self.assertRaisesRegex(ValueError, "duplicate owned declaration"):
            self.export()
        self.assertEqual(self.output.read_text(), "previous complete export")
        self.assertEqual(json.loads((self.data / "export-status.json").read_text())["state"], "error")

    def test_bad_shard_identity_and_missing_summary_do_not_publish(self):
        for problem in ("identity", "summary"):
            with self.subTest(problem=problem):
                self.manifest["content_hash"] = problem
                self.output.write_text("old", encoding="utf-8")
                def corrupt(records, index):
                    if index == 1:
                        if problem == "identity":
                            records[0]["shard_index"] = 0
                        else:
                            records.pop()
                self.records_hook = corrupt
                with self.assertRaises(ValueError):
                    self.export()
                self.assertEqual(self.output.read_text(), "old")
                status = json.loads((self.data / "export-status.json").read_text())
                part = Path(status["part_directory"]) / "part-00001.status.json"
                self.assertEqual(json.loads(part.read_text())["state"], "error")

    def test_failed_writer_reports_returncode_and_keeps_previous_export(self):
        self.output.write_text("old", encoding="utf-8")
        original = self.fake_run
        def fail(command, **kwargs):
            if command[command.index("--shard-index") + 1] == "1":
                raise subprocess.CalledProcessError(7, command)
            return original(command, **kwargs)
        self.run.side_effect = fail
        with self.assertRaises(subprocess.CalledProcessError):
            self.export()
        status = json.loads((self.data / "export-status.json").read_text())
        receipt = Path(status["part_directory"]) / "part-00001.status.json"
        self.assertEqual(json.loads(receipt.read_text())["returncode"], 7)
        self.assertEqual(self.output.read_text(), "old")

    def test_module_selection_does_not_claim_complete_project(self):
        result = self.export(module="OTSelector.Geometry", jobs=1)
        self.assertTrue(result["summary"]["complete"])
        self.assertFalse(result["summary"]["full_corpus"])
        self.assertEqual(result["summary"]["export_scope"], "module_selection")

    def test_global_owned_count_must_match_merged_partition(self):
        self.records_hook = lambda records, index: records[-1].update(project_owned_count=100)
        with self.assertRaisesRegex(ValueError, "complete project count"):
            self.export()
        self.assertFalse(self.output.exists())


class NativeCacheTests(unittest.TestCase):
    def test_native_binary_cache_compiles_atomically_without_real_lean(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "project"
            root.mkdir()
            (root / "lean-toolchain").write_text("lean-test\n", encoding="utf-8")
            data = Path(tmp) / "index"
            def compile_fake(command, **kwargs):
                flag = "-o" if "-o" in command else "-c"
                Path(command[command.index(flag) + 1]).write_text("compiled", encoding="utf-8")
                return subprocess.CompletedProcess(command, 0)
            with patch.object(exporting.subprocess, "run", side_effect=compile_fake) as run:
                first = exporting.native_extractor(root, data)
                self.assertTrue(first.is_file())
                self.assertEqual(exporting.native_extractor(root, data), first)
                self.assertEqual(run.call_count, 2)


if __name__ == "__main__":
    unittest.main()
