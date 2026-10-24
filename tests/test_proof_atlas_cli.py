"""CLI artifact reuse and failure recovery without invoking Lean or embeddings."""

from contextlib import ExitStack
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from tools.proof_atlas import cli
from tools.proof_atlas.store import Store


class CliTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "project"
        self.data = Path(self.temp.name) / "index"
        for module in ("Demo", "Other"):
            path = self.root / module / "One.lean"
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("-- test input\n", encoding="utf-8")
        self.manifest = {"sources": {"Demo/One.lean": "source-v1", "Other/One.lean": "other-v1"},
                         "toolchain": "lean-test", "mathlib_revision": "mathlib-test",
                         "content_hash": "stable-mathematical-source-content"}
        context = ExitStack()
        self.addCleanup(context.close)
        self.manifest_mock = context.enter_context(patch.object(cli, "source_manifest", return_value=self.manifest))
        self.extract = context.enter_context(patch.object(cli, "_extract", side_effect=self.complete_extract))
        self.embed = context.enter_context(patch.object(cli, "_embed", return_value={"status": "disabled"}))
        self.process = context.enter_context(patch.object(
            cli.subprocess, "run", return_value=subprocess.CompletedProcess([], 0)))
        context.enter_context(patch.object(cli, "_progress"))

    def args(self, command, *extra, data=None):
        return cli.parser().parse_args([command, "--project-root", str(self.root),
                                        "--data-dir", str(data or self.data), *map(str, extra)])

    @staticmethod
    def write_records(output, records):
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text("".join(json.dumps(record) + "\n" for record in records), encoding="utf-8")

    def complete_extract(self, args, command, output, extra):
        module = "Demo.One" if command == "export" else extra[extra.index("--module") + 1]
        name = "Demo.keep" if command == "export" else (args.name or "Demo.keep")
        records = [{"record_type": "declaration", "name": name, "module": module,
                    "kind": "theorem", "range": {"start": {"line": 1}},
                    "type_text": "True", "type_dependencies": [], "proof_dependencies": []}]
        if command in ("detail", "trace"):
            records.append({"record_type": "triad", "declaration": name,
                            "ordered_telescope": [], "target_text": "True",
                            "target_expr": {"kind": "const", "name": "True"},
                            "proof_skeleton": {"head": "True.intro", "expression_text": "True.intro",
                                               "arguments": []}})
        if command == "trace":
            records.append({"record_type": "proof_fragment", "declaration": name,
                            "source": "exact True.intro", "syntax_kind": "exact",
                            "goals_before": [{"id": "g0", "target_text": "True", "hypotheses": []}],
                            "goals_after": []})
        records.append({"record_type": "summary", "complete": True})
        self.write_records(output, records)

    def build(self, *extra):
        return cli.dispatch(self.args("build", "--embedding", "none", "--jobs", "1", *extra))

    def test_default_build_routes_parallel_export_through_driver(self):
        def corpus(args, output, module, triads, jobs):
            self.complete_extract(args, "export", output, [])
            return {"summary": {"complete": True}}
        with patch("tools.proof_atlas.exporting.export_corpus", side_effect=corpus) as driver:
            cli.dispatch(self.args("build", "--embedding", "none"))
        self.assertEqual(driver.call_args.kwargs.get("jobs", driver.call_args.args[-1]), 4)
        self.extract.assert_not_called()

    def test_export_cache_tracks_module_triads_and_extractor_revision(self):
        self.build()
        self.build()
        self.assertEqual(self.extract.call_count, 1)
        self.build("--triads", "all")
        self.assertEqual(self.extract.call_count, 2)
        self.build("--triads", "all", "--module", "Demo.One")
        self.assertEqual(self.extract.call_count, 3)
        receipt = self.data / "export.sources.json"
        binding = json.loads(receipt.read_text())
        binding["selection"]["extractor_sha256"] = "previous-extractor"
        receipt.write_text(json.dumps(binding), encoding="utf-8")
        self.build("--triads", "all", "--module", "Demo.One")
        self.assertEqual(self.extract.call_count, 4)

    def test_summary_must_be_complete_and_at_eof(self):
        output = Path(self.temp.name) / "export.jsonl"
        for contents, expected in (
                ("", False), ("not JSON\n", False), ("[]\n", False),
                ('{"record_type":"summary","complete":false}\n', False),
                ('{"record_type":"summary","complete":true}\n', True),
                ('{"record_type":"summary","complete":true}\n{"record_type":"declaration"}\n', False),
                ('{"record_type":"summary","complete":true}\n{"record_type":', False)):
            with self.subTest(contents=contents):
                output.write_text(contents, encoding="utf-8")
                self.assertEqual(cli._completed(output), expected)

    def test_extractor_failure_keeps_previous_completed_export_receipt_and_database(self):
        self.build()
        output, receipt = self.data / "export.jsonl", self.data / "export.sources.json"
        before = (output.read_bytes(), receipt.read_bytes())

        def failing(args, command, pending, extra):
            pending.write_text('{"record_type":"declaration","name":"partial"}\n', encoding="utf-8")
            raise subprocess.CalledProcessError(1, ["lean"])

        self.extract.side_effect = failing
        with self.assertRaises(subprocess.CalledProcessError):
            self.build("--refresh")
        self.assertEqual((output.read_bytes(), receipt.read_bytes()), before)
        with Store(self.data / "atlas.sqlite3") as store:
            self.assertIsNotNone(store.get_decl("Demo.keep"))
            self.assertIsNone(store.get_decl("partial"))

    def test_incomplete_success_cannot_replace_completed_export(self):
        self.build()
        output, receipt = self.data / "export.jsonl", self.data / "export.sources.json"
        before = (output.read_bytes(), receipt.read_bytes())
        self.extract.side_effect = lambda args, command, pending, extra: pending.write_text(
            '{"record_type":"declaration","name":"partial"}\n', encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "complete summary"):
            self.build("--refresh")
        self.assertEqual((output.read_bytes(), receipt.read_bytes()), before)

    def test_partial_trace_failure_preserves_completed_trace_and_binding(self):
        self.build()
        args = lambda: self.args("trace", self.root / "Demo/One.lean", "--name", "Demo.keep")
        cli.dispatch(args())
        saved = next((self.data / "traces").glob("*.jsonl"))
        receipt = saved.with_suffix(".sources.json")
        before = (saved.read_bytes(), receipt.read_bytes())

        def failing(args, command, pending, extra):
            pending.write_text("partial trace", encoding="utf-8")
            raise subprocess.CalledProcessError(1, ["lean"])

        self.extract.side_effect = failing
        with self.assertRaises(subprocess.CalledProcessError):
            cli.dispatch(args())
        self.assertEqual((saved.read_bytes(), receipt.read_bytes()), before)
        self.assertEqual(self.extract.call_args.args[2].suffixes[-2:], [".pending", ".jsonl"])

    def test_trace_cache_distinguishes_module_paths_and_declaration_selection(self):
        self.build()
        for path, name in (("Demo/One.lean", "Demo.keep"), ("Other/One.lean", "Other.keep"),
                           ("Demo/One.lean", "Demo.another")):
            cli.dispatch(self.args("trace", self.root / path, "--name", name))
        outputs = list((self.data / "traces").glob("*.jsonl"))
        self.assertEqual(len(outputs), 3)
        self.assertEqual(len({path.name for path in outputs}), 3)
        self.assertTrue(all(cli._completed(path) for path in outputs))

    def test_rebuild_replays_bound_detail_records_and_omits_full_manifest_from_stats(self):
        result = self.build()
        self.assertNotIn("manifest", result["stats"]["snapshot"])
        cli.dispatch(self.args("detail", "Demo.keep", "--module", "Demo.One"))
        with Store(self.data / "atlas.sqlite3") as store:
            self.assertIsNotNone(store.get_triad("Demo.keep"))
        result = self.build()
        with Store(self.data / "atlas.sqlite3") as store:
            self.assertIsNotNone(store.get_triad("Demo.keep"))
        self.assertEqual(result["stats"]["triads"], 1)

    def test_generated_data_cannot_be_inside_project_even_via_symlink(self):
        link = Path(self.temp.name) / "linked-project"
        link.symlink_to(self.root, target_is_directory=True)
        for location in (self.root, self.root / "generated", link / "generated"):
            with self.subTest(location=location):
                with self.assertRaisesRegex(ValueError, "outside the repository"):
                    cli.dispatch(self.args("build", "--embedding", "none", data=location))
        self.extract.assert_not_called()
        self.assertFalse((self.root / "generated").exists())


if __name__ == "__main__":
    unittest.main()
