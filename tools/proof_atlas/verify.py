"""Run a proof candidate in the project's actual Lean environment.

Incomplete candidates remain metavariable trials: ``partial`` never means that
Lean accepted a theorem. Only a closed expression checked by the kernel and the
project's axiom policy receives ``complete``. No workspace source is modified.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Any
import uuid


SCHEMA_VERSION = 1
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
_MODULE_NAME = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*\Z")
_FORBIDDEN = re.compile(r"(?<![\w'])\b(sorry|admit|axiom|constant|sorryAx)\b(?![\w'])")
_HELPER = Path(__file__).with_name("lean") / "Check.lean"
_PATTERNS = Path(__file__).with_name("patterns.json")


def _lean_code_only(source: str) -> str:
    """Mask nested comments and strings before checking forbidden placeholders."""
    result: list[str] = []
    index = 0
    depth = 0
    in_string = False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string:
            if char == "\\" and index + 1 < len(source):
                result.extend("  ")
                index += 2
            else:
                if char == '"':
                    in_string = False
                result.append("\n" if char == "\n" else " ")
                index += 1
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            if end == -1:
                end = len(source)
            result.extend(" " * (end - index))
            index = end
        elif char == '"':
            in_string = True
            result.append(" ")
            index += 1
        else:
            result.append(char)
            index += 1
    return "".join(result)


def _validate_request(request: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(request, dict):
        raise ValueError("request must be a JSON object")
    imports = request.get("imports", [])
    if not isinstance(imports, list) or not all(
        isinstance(module, str) and _MODULE_NAME.fullmatch(module) for module in imports
    ):
        raise ValueError("imports must contain Lean module names")
    context = request.get("context", "")
    goal = request.get("goal")
    candidate = request.get("candidate")
    kind = request.get("candidate_kind", "tactic")
    if not isinstance(context, str):
        raise ValueError("context must be Lean source text")
    if not isinstance(goal, str) or not goal.strip():
        raise ValueError("goal must be nonempty Lean source text")
    if not isinstance(candidate, str) or not candidate.strip():
        raise ValueError("candidate must be nonempty Lean source text")
    if kind not in {"tactic", "term"}:
        raise ValueError("candidate_kind must be 'tactic' or 'term'")
    mapping = request.get("object_mapping", {})
    if not isinstance(mapping, dict) or not all(
        isinstance(role, str) and isinstance(expression, str)
        for role, expression in mapping.items()
    ):
        raise ValueError("object_mapping must map role names to Lean expressions")
    obligations = request.get("remaining_obligations", [])
    if not isinstance(obligations, list) or not all(isinstance(x, str) for x in obligations):
        raise ValueError("remaining_obligations must be a list of descriptions")
    for label, source in (("context", context), ("goal", goal), ("candidate", candidate)):
        forbidden = _FORBIDDEN.search(_lean_code_only(source))
        if forbidden:
            raise ValueError(f"{label} contains forbidden placeholder/declaration: {forbidden[1]}")
    for role, expression in mapping.items():
        forbidden = _FORBIDDEN.search(_lean_code_only(expression))
        if forbidden:
            raise ValueError(f"object_mapping {role!r} contains forbidden placeholder/declaration")
    return {
        "imports": list(dict.fromkeys(imports)),
        "context": context,
        "goal": goal,
        "candidate": candidate,
        "candidate_kind": kind,
        "object_mapping": dict(mapping),
        "remaining_obligations": list(obligations),
    }


def render_trial(request: dict[str, Any], token: str) -> str:
    """Create a standalone trial without changing its supplied context or goal."""
    request = _validate_request(request)
    helper = _HELPER.read_text(encoding="utf-8")
    helper_body = "\n".join(
        line for line in helper.splitlines() if not line.startswith("import ")
    )
    modules = list(dict.fromkeys(["Lean", "Lean.Util.CollectAxioms", *request["imports"]]))
    candidate = request["candidate"]
    if request["candidate_kind"] == "term":
        candidate = f"exact ({candidate})"
    tactic_lines = "\n".join("  " + line for line in candidate.splitlines())
    mapping_commands = "\n".join(
        f'#proof_atlas_object "{token}" {json.dumps(role, ensure_ascii=False)} := {expression}'
        for role, expression in request["object_mapping"].items()
    )
    return (
        "\n".join(f"import {module}" for module in modules)
        + "\n\n"
        + helper_body
        + "\n\nset_option autoImplicit false\n"
        + request["context"]
        + "\n\n"
        + mapping_commands
        + f'\n\n#proof_atlas_check "{token}" : {request["goal"]} := by\n'
        + tactic_lines
        + "\n"
    )


def load_patterns(path: str | Path | None = None) -> list[dict[str, Any]]:
    """Read the curated conditions/objects/proof_detail pattern library."""
    payload = json.loads(Path(path or _PATTERNS).read_text(encoding="utf-8"))
    if payload.get("schema_version") != SCHEMA_VERSION:
        raise ValueError("unsupported pattern schema_version")
    patterns = payload.get("patterns")
    if not isinstance(patterns, list):
        raise ValueError("pattern library must contain a patterns list")
    seen: set[str] = set()
    for pattern in patterns:
        if not isinstance(pattern, dict) or not all(
            name in pattern for name in ("id", "conditions", "objects", "proof_detail")
        ):
            raise ValueError("patterns require id, conditions, objects and proof_detail")
        if pattern["id"] in seen:
            raise ValueError(f"duplicate pattern id: {pattern['id']}")
        seen.add(pattern["id"])
    return patterns


def verify_candidate(
    request: dict[str, Any],
    project_root: str | Path = ".",
    timeout_seconds: float = 60,
    lake_executable: str = "lake",
) -> dict[str, Any]:
    """Return a real Lean trial result: complete, partial, or rejected.

    ``object_mapping`` and ``remaining_obligations`` record the caller's
    explicit mapping and proposed obligations; they are never used as proof
    evidence. ``remaining_goals`` always comes from Lean's metavariable state.
    The generated file is temporary and is removed after the command finishes.
    """
    result: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "status": "rejected",
        "kernel_checked": False,
        "remaining_goals": [],
        "remaining_goal_types": [],
        "axioms": [],
        "object_mapping": {},
        "typed_object_mapping": {},
        "declared_remaining_obligations": [],
        "validation": {"engine": "Lean", "command": [], "returncode": None,
                       "diagnostics": "", "temporary_trial": True},
    }
    try:
        normalized = _validate_request(request)
        if not isinstance(timeout_seconds, (int, float)) or not math.isfinite(timeout_seconds):
            raise ValueError("timeout_seconds must be a positive finite number")
        if timeout_seconds <= 0:
            raise ValueError("timeout_seconds must be a positive finite number")
        root = Path(project_root).resolve(strict=True)
        if not root.is_dir() or not (root / "lean-toolchain").is_file():
            raise ValueError("project_root must be a Lean project with lean-toolchain")
        result["object_mapping"] = normalized["object_mapping"]
        result["declared_remaining_obligations"] = normalized["remaining_obligations"]
        result["goal"] = normalized["goal"]
        result["candidate_kind"] = normalized["candidate_kind"]
        result["validation"].update({
            "project_root": str(root),
            "toolchain": (root / "lean-toolchain").read_text(encoding="utf-8").strip(),
            "request_sha256": hashlib.sha256(json.dumps(
                normalized, ensure_ascii=False, sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")).hexdigest(),
            "helper_sha256": hashlib.sha256(_HELPER.read_bytes()).hexdigest(),
        })
        token = uuid.uuid4().hex
        source = render_trial(normalized, token)
        with tempfile.TemporaryDirectory(prefix="proof-atlas-", dir="/tmp") as directory:
            trial = Path(directory) / "Trial.lean"
            trial.write_text(source, encoding="utf-8")
            command = [lake_executable, "env", "lean", str(trial)]
            result["validation"]["command"] = command
            try:
                process = subprocess.run(
                    command, cwd=root, capture_output=True, text=True,
                    timeout=timeout_seconds, check=False,
                )
            except subprocess.TimeoutExpired as error:
                stdout = error.stdout or ""
                stderr = error.stderr or ""
                if isinstance(stdout, bytes):
                    stdout = stdout.decode("utf-8", errors="replace")
                if isinstance(stderr, bytes):
                    stderr = stderr.decode("utf-8", errors="replace")
                result["validation"]["diagnostics"] = stdout + stderr
                result["reason"] = "Lean trial timed out; no proof was certified"
                return result
            result["validation"]["returncode"] = process.returncode
            marker = f"PROOF_ATLAS_JSON[{token}] "
            object_marker = f"PROOF_ATLAS_OBJECT[{token}] "
            records = [line.split(marker, 1)[1] for line in process.stdout.splitlines()
                       if marker in line]
            diagnostics = "\n".join(
                line for line in process.stdout.splitlines()
                if marker not in line and object_marker not in line
            )
            result["validation"]["diagnostics"] = diagnostics + process.stderr
            objects = [json.loads(line.split(object_marker, 1)[1])
                       for line in process.stdout.splitlines() if object_marker in line]
            roles = [obj.get("role") for obj in objects if isinstance(obj, dict)]
            if len(roles) != len(normalized["object_mapping"]) or set(roles) != set(
                normalized["object_mapping"]
            ):
                result["reason"] = "Lean could not check every supplied object mapping"
                return result
            for obj in objects:
                if not obj.get("kernel_checked") or not isinstance(obj.get("inferred_type"), str):
                    result["reason"] = "Lean did not certify a mapped object's inferred type"
                    return result
                extra_axioms = set(obj.get("axioms", [])) - ALLOWED_AXIOMS
                if extra_axioms:
                    result["reason"] = "mapped object uses disallowed axioms: " + ", ".join(
                        sorted(extra_axioms)
                    )
                    return result
                result["typed_object_mapping"][obj["role"]] = {
                    "expression": normalized["object_mapping"][obj["role"]],
                    "elaborated_expression": obj.get("elaborated_expression", ""),
                    "inferred_type": obj["inferred_type"],
                    "kernel_checked": True,
                }
            if len(records) != 1:
                result["reason"] = "Lean did not emit exactly one proof-state result"
                return result
            backend = json.loads(records[0])
            if not isinstance(backend, dict):
                raise ValueError("Lean proof-state result was not an object")
            status = backend.get("status")
            if status not in {"complete", "partial", "rejected"}:
                raise ValueError("Lean emitted an unknown proof-state status")
            for key in ("remaining_goals", "remaining_goal_types", "axioms"):
                values = backend.get(key)
                if not isinstance(values, list) or not all(isinstance(x, str) for x in values):
                    raise ValueError(f"Lean emitted invalid {key}")
                result[key] = values
            result["elaborated_goal"] = backend.get("target", "")
            if backend.get("error"):
                result["reason"] = backend["error"]
            if process.returncode != 0:
                result["reason"] = "Lean exited with errors; no proof was certified"
                return result
            if status == "complete":
                if not backend.get("kernel_checked") or result["remaining_goals"]:
                    result["reason"] = "inconsistent complete result from Lean"
                    return result
                forbidden_axioms = sorted(set(result["axioms"]) - ALLOWED_AXIOMS)
                if forbidden_axioms:
                    result["reason"] = "disallowed transitive axioms: " + ", ".join(forbidden_axioms)
                    return result
                result["status"] = "complete"
                result["kernel_checked"] = True
            elif status == "partial":
                if not result["remaining_goals"]:
                    result["reason"] = "partial result omitted its actual remaining goals"
                    return result
                result["status"] = "partial"
                result["reason"] = "candidate leaves Lean goals; no complete proof was certified"
            return result
    except (ValueError, OSError, UnicodeError) as error:
        result["status"] = "rejected"
        result["kernel_checked"] = False
        result["reason"] = str(error)
        return result


def _contains_truncated(value: Any) -> bool:
    pending = [value]
    while pending:
        current = pending.pop()
        if isinstance(current, dict):
            if current.get("kind") == "truncated":
                return True
            pending.extend(current.values())
        elif isinstance(current, list):
            pending.extend(current)
    return False


def elaborate_state(
    request: dict[str, Any],
    project_root: str | Path = ".",
    timeout_seconds: float = 60,
    lake_executable: str = "lake",
) -> dict[str, Any]:
    """Elaborate a new goal and its context into the exporter's typed DAG schema.

    This checks a *type*, not a proof. It never accepts a candidate or asserts a
    theorem. Local identifiers are exported in context order as ``b0``, ``b1``,
    ...; names are separate diagnostics. ``expr_budget`` defaults to 10000 unique
    expression nodes per exported expression. Zero means unlimited. Any omitted
    expression subtree is explicitly marked ``truncated`` and reported via
    ``ast_truncated``; it cannot silently support a structural proof transfer.
    """
    result: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "status": "rejected",
        "state_elaborated": False,
        "kernel_checked": False,
        "type_kernel_checked": False,
        "ordered_telescope": [],
        "validation": {"engine": "Lean", "command": [], "returncode": None,
                       "diagnostics": "", "temporary_trial": True},
    }
    try:
        if not isinstance(request, dict):
            raise ValueError("request must be a JSON object")
        normalized = _validate_request(dict(request, candidate="skip", candidate_kind="tactic"))
        budget = request.get("expr_budget", 10000)
        if not isinstance(budget, int) or isinstance(budget, bool) or budget < 0:
            raise ValueError("expr_budget must be a nonnegative integer (zero means unlimited)")
        if not isinstance(timeout_seconds, (int, float)) or not math.isfinite(timeout_seconds):
            raise ValueError("timeout_seconds must be a positive finite number")
        if timeout_seconds <= 0:
            raise ValueError("timeout_seconds must be a positive finite number")
        root = Path(project_root).resolve(strict=True)
        if not root.is_dir() or not (root / "lean-toolchain").is_file():
            raise ValueError("project_root must be a Lean project with lean-toolchain")
        state_input = {key: normalized[key] for key in ("imports", "context", "goal")}
        state_input["expr_budget"] = budget
        result.update(state_input)
        result["object_mapping"] = normalized["object_mapping"]
        helper = _HELPER.read_text(encoding="utf-8")
        body = "\n".join(line for line in helper.splitlines() if not line.startswith("import "))
        modules = list(dict.fromkeys(["Lean", "Lean.Util.CollectAxioms", *normalized["imports"]]))
        token = uuid.uuid4().hex
        source = (
            "\n".join(f"import {module}" for module in modules)
            + "\n\n" + body + "\n\nset_option autoImplicit false\n"
            + normalized["context"]
            + f'\n\n#proof_atlas_state "{token}" {budget} : {normalized["goal"]}\n'
        )
        result["validation"].update({
            "project_root": str(root),
            "toolchain": (root / "lean-toolchain").read_text(encoding="utf-8").strip(),
            "request_sha256": hashlib.sha256(json.dumps(
                state_input, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
            ).encode("utf-8")).hexdigest(),
            "helper_sha256": hashlib.sha256(helper.encode("utf-8")).hexdigest(),
        })
        with tempfile.TemporaryDirectory(prefix="proof-atlas-state-", dir="/tmp") as directory:
            trial = Path(directory) / "State.lean"
            trial.write_text(source, encoding="utf-8")
            command = [lake_executable, "env", "lean", str(trial)]
            result["validation"]["command"] = command
            try:
                process = subprocess.run(
                    command, cwd=root, capture_output=True, text=True,
                    timeout=timeout_seconds, check=False,
                )
            except subprocess.TimeoutExpired as error:
                stdout, stderr = error.stdout or "", error.stderr or ""
                if isinstance(stdout, bytes):
                    stdout = stdout.decode("utf-8", errors="replace")
                if isinstance(stderr, bytes):
                    stderr = stderr.decode("utf-8", errors="replace")
                result["validation"]["diagnostics"] = stdout + stderr
                result["reason"] = "Lean state elaboration timed out; no typed state was exported"
                return result
            result["validation"]["returncode"] = process.returncode
            marker = f"PROOF_ATLAS_STATE[{token}] "
            records = [line.split(marker, 1)[1] for line in process.stdout.splitlines()
                       if marker in line]
            result["validation"]["diagnostics"] = "\n".join(
                line for line in process.stdout.splitlines() if marker not in line
            ) + process.stderr
            if process.returncode != 0:
                result["reason"] = "Lean exited with errors; no typed state was exported"
                return result
            if len(records) != 1:
                result["reason"] = "Lean did not emit exactly one elaborated state"
                return result
            backend = json.loads(records[0])
            if not isinstance(backend, dict) or backend.get("status") != "elaborated":
                raise ValueError("Lean emitted an invalid typed state")
            binders = backend.get("ordered_telescope")
            if not isinstance(binders, list):
                raise ValueError("Lean state omitted the ordered telescope")
            for index, binder in enumerate(binders):
                if not isinstance(binder, dict) or binder.get("id") != f"b{index}":
                    raise ValueError("Lean state emitted noncanonical binder IDs")
                if binder.get("role") not in {"object", "condition"}:
                    raise ValueError("Lean state emitted an unknown binder classification")
                if not isinstance(binder.get("type_expr"), dict):
                    raise ValueError("Lean state omitted an actual binder type expression")
            for key in ("target_expr", "type_expr"):
                if not isinstance(backend.get(key), dict) or backend[key].get("kind") != "dag":
                    raise ValueError(f"Lean state omitted its actual {key}")
            if not backend.get("type_kernel_checked"):
                raise ValueError("Lean did not kernel-check the goal type")
            result.update(backend)
            result["kernel_checked"] = False
            result["ast_truncated"] = _contains_truncated({
                key: backend[key] for key in ("ordered_telescope", "target_expr", "type_expr")
            })
            result["expr_budget_per_expression"] = True
            return result
    except (ValueError, OSError, UnicodeError) as error:
        result["status"] = "rejected"
        result["state_elaborated"] = False
        result["kernel_checked"] = False
        result["type_kernel_checked"] = False
        result["reason"] = str(error)
        return result
