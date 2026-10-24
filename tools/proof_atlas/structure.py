"""Conservative structural operations on exported Lean expressions.

These operations compare syntax, never Lean ``isDefEq`` or theorem equivalence.
The matching fragment has rigid constant function symbols and object variables
from an ordered telescope. Nonidentical binders, higher-order applications and
unresolved metavariables are explicitly unsupported. Unknown substitution types
and unmatched conditions remain obligations for a subsequent Lean trial.
"""

from __future__ import annotations

import hashlib
import json
from collections import defaultdict
from typing import Any, Iterable, Mapping, Sequence

Expr = dict[str, Any]


class UnsupportedExpression(ValueError):
    """The exported syntax is outside the documented structural fragment."""


def _key(value: Any) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def _syntax_digest(value: Any, memo: dict | None = None) -> str:
    """Merkle hash JSON syntax without expanding shared expression subgraphs."""
    memo = {} if memo is None else memo
    if isinstance(value, (dict, list)):
        identity = id(value)
        if identity in memo:
            return memo[identity][1]
        if isinstance(value, dict):
            body = ["dict", *[[key, _syntax_digest(value[key], memo)] for key in sorted(value)]]
        else:
            body = ["list", *[_syntax_digest(item, memo) for item in value]]
        result = hashlib.sha256(_key(body).encode()).hexdigest()
        # Retain the object too: temporary substituted trees must not permit
        # Python object-ID reuse to hit a stale digest in a shared memo.
        memo[identity] = (value, result)
        return result
    return hashlib.sha256(_key([type(value).__name__, value]).encode()).hexdigest()


def _same(left: Any, right: Any, memo: dict | None = None) -> bool:
    memo = {} if memo is None else memo
    return _syntax_digest(left, memo) == _syntax_digest(right, memo)


_CHILD_FIELDS = {"app": ("fn", "arg"), "lam": ("type", "body"),
                 "forallE": ("type", "body"), "letE": ("type", "value", "body"),
                 "proj": ("struct",), "mdata": ("expr",), "hole": ("type_expr",)}


def compact_expression(expr: Expr) -> Expr:
    """Serialize shared normalized ASTs as expr_dag_v1, never an expanded tree."""
    nodes: list[Expr] = []
    ids: dict[int, int] = {}
    shared = False

    def visit(node: Expr) -> int:
        nonlocal shared
        identity = id(node)
        if identity in ids:
            shared = True
            return ids[identity]
        item = dict(node)
        for field in _CHILD_FIELDS.get(node["kind"], ()):
            if isinstance(node.get(field), dict):
                item[field] = {"kind": "ref", "id": visit(node[field])}
        index = len(nodes)
        nodes.append(item)
        ids[identity] = index
        return index

    root = visit(expr)
    return {"kind": "dag", "root": root, "nodes": nodes} if shared else expr


def _pack_result(value: Any) -> Any:
    if isinstance(value, dict):
        if value.get("kind") in {"app", "lam", "forallE", "letE", "proj", "hole"}:
            return compact_expression(value)
        return {key: _pack_result(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_pack_result(item) for item in value]
    return value


class _Normalizer:
    def __init__(self, universe_params: Sequence[str], max_nodes: int):
        self.fvars: dict[str, str] = {}
        self.levels = {name: f"u{i}" for i, name in enumerate(universe_params)}
        self.remaining = max_nodes
        self.dag_scope: dict[str, Any] | None = None

    def tick(self) -> None:
        self.remaining -= 1
        if self.remaining < 0:
            raise UnsupportedExpression("node budget exceeded")

    def level(self, level: Mapping[str, Any]) -> Expr:
        self.tick()
        kind = level.get("kind")
        if kind == "zero":
            return {"kind": kind}
        if kind == "param":
            name = level["name"]
            return {"kind": kind, "name": self.levels.setdefault(name, f"u{len(self.levels)}")}
        if kind == "succ":
            return {"kind": kind, "of": self.level(level["of"])}
        if kind in {"max", "imax"}:
            return {"kind": kind, "left": self.level(level["left"]),
                    "right": self.level(level["right"])}
        raise UnsupportedExpression(f"unsupported universe level: {kind}")

    def expr(self, expr: Mapping[str, Any]) -> Expr:
        kind = expr.get("kind")
        if kind == "dag":
            nodes = expr["nodes"]
            if not isinstance(nodes, list):
                raise UnsupportedExpression("DAG nodes must be an array")
            previous = self.dag_scope
            self.dag_scope = {"nodes": nodes, "memo": {}, "active": set()}
            try:
                result = self.reference(expr["root"])
                # Reject malformed unused nodes too; do not assume exporter order.
                for index in range(len(nodes)):
                    self.reference(index)
                return result
            finally:
                self.dag_scope = previous
        if kind == "ref":
            return self.reference(expr["id"])
        self.tick()
        if kind == "mdata":
            return self.expr(expr["expr"])
        if kind == "bvar":
            index = expr["index"]
            if not isinstance(index, int) or isinstance(index, bool) or index < 0:
                raise UnsupportedExpression("invalid bound-variable index")
            return {"kind": kind, "index": index}
        if kind == "fvar":
            if expr["id"] not in self.fvars:
                raise UnsupportedExpression(f"free variable absent from telescope: {expr['id']}")
            return {"kind": kind, "id": self.fvars[expr["id"]]}
        if kind == "const":
            if not isinstance(expr["name"], str) or not expr["name"]:
                raise UnsupportedExpression("invalid constant name")
            return {"kind": kind, "name": expr["name"],
                    "levels": [self.level(level) for level in expr.get("levels", [])]}
        if kind == "sort":
            return {"kind": kind, "level": self.level(expr["level"])}
        if kind == "app":
            return {"kind": kind, "fn": self.expr(expr["fn"]), "arg": self.expr(expr["arg"])}
        if kind in {"lam", "forallE"}:
            return {"kind": kind, "binder_info": expr["binder_info"],
                    "type": self.expr(expr["type"]), "body": self.expr(expr["body"])}
        if kind == "letE":
            return {"kind": kind, "nondep": expr["nondep"], "type": self.expr(expr["type"]),
                    "value": self.expr(expr["value"]), "body": self.expr(expr["body"])}
        if kind == "proj":
            if not isinstance(expr["index"], int) or expr["index"] < 0:
                raise UnsupportedExpression("invalid projection index")
            return {"kind": kind, "type_name": expr["type_name"], "index": expr["index"],
                    "struct": self.expr(expr["struct"])}
        if kind == "lit":
            literal_kind, value = expr["literal_kind"], expr["value"]
            if literal_kind == "nat":
                if isinstance(value, bool) or not str(value).isdigit():
                    raise UnsupportedExpression("invalid natural literal")
                value = int(value)
            elif literal_kind != "string" or not isinstance(value, str):
                raise UnsupportedExpression("unsupported literal")
            return {"kind": kind, "literal_kind": literal_kind, "value": value}
        raise UnsupportedExpression(f"unsupported expression: {kind}")

    def reference(self, index: Any) -> Expr:
        scope = self.dag_scope
        if scope is None:
            raise UnsupportedExpression("expression reference outside a DAG")
        if not isinstance(index, int) or isinstance(index, bool) or not 0 <= index < len(scope["nodes"]):
            raise UnsupportedExpression("invalid DAG reference")
        if index in scope["active"]:
            raise UnsupportedExpression("cyclic expression DAG")
        if index not in scope["memo"]:
            scope["active"].add(index)
            try:
                scope["memo"][index] = self.expr(scope["nodes"][index])
            finally:
                scope["active"].remove(index)
        return scope["memo"][index]

    def context(self, binders: Sequence[Mapping[str, Any]]) -> list[Expr]:
        result = []
        for index, binder in enumerate(binders):
            if binder.get("index", index) != index or binder["id"] in self.fvars:
                raise UnsupportedExpression("invalid ordered telescope")
            if binder.get("role") not in {"condition", "object"}:
                raise UnsupportedExpression("unknown telescope binder role")
            item = {"id": f"b{index}", "index": index,
                    "binder_mode": binder["binder_mode"], "role": binder["role"],
                    "type_expr": self.expr(binder["type_expr"])}
            dependencies = binder.get("depends_on", [])
            if any(dep not in self.fvars for dep in dependencies):
                raise UnsupportedExpression("telescope dependency is not an earlier binder")
            # The expression already contains dependencies; a separate unordered
            # diagnostic list must not change an expression's fingerprint.
            if binder.get("is_let", False):
                item.update(is_let=True, value_expr=self.expr(binder["value_expr"]))
            self.fvars[binder["id"]] = item["id"]
            result.append(item)
        return result


def alpha_normalize(expr: Mapping[str, Any], binders: Sequence[Mapping[str, Any]] = (),
                    universe_params: Sequence[str] = (), *, max_nodes: int = 10000) -> Expr:
    """Remove printed names while retaining context order and expression syntax.

    ``mdata`` is transparent metadata; lets, lambdas, projections, constants,
    explicitness and universe expressions remain. No constant is unfolded and
    no beta/eta reduction, proposition erasure or proof irrelevance is applied.
    """
    try:
        norm = _Normalizer(universe_params, max_nodes)
        context = norm.context(binders)
        normalized = norm.expr(expr)
        return {"ordered_telescope": context, "expr": normalized,
                "universe_params": [f"u{i}" for i in range(len(norm.levels))]}
    except (KeyError, TypeError, AttributeError, RecursionError) as exc:
        raise UnsupportedExpression(f"malformed or excessively deep expression: {exc}") from exc


def alpha_fingerprint(expr: Mapping[str, Any], binders: Sequence[Mapping[str, Any]] = (),
                      universe_params: Sequence[str] = (), *, max_nodes: int = 10000) -> str:
    """SHA256 of alpha-normalized *syntax*, including the ordered telescope."""
    return _syntax_digest(alpha_normalize(expr, binders, universe_params, max_nodes=max_nodes))


def compare_structure(left: Mapping[str, Any], right: Mapping[str, Any], *,
                      left_binders: Sequence[Mapping[str, Any]] = (),
                      right_binders: Sequence[Mapping[str, Any]] = (),
                      max_nodes: int = 10000) -> Expr:
    """Check exact alpha syntax, without claiming semantic equivalence."""
    try:
        a = alpha_fingerprint(left, left_binders, max_nodes=max_nodes)
        b = alpha_fingerprint(right, right_binders, max_nodes=max_nodes)
        return {"status": "exact" if a == b else "unverified",
                "comparison": "alpha-normalized syntax", "left": a, "right": b}
    except UnsupportedExpression as exc:
        return {"status": "unsupported", "reason": str(exc)}


def _first_order(expr: Expr, visited: set[int] | None = None) -> None:
    visited = set() if visited is None else visited
    if id(expr) in visited:
        return
    visited.add(id(expr))
    kind = expr["kind"]
    if kind in {"const", "fvar", "lit"}:
        return
    if kind == "app":
        head = expr
        while head["kind"] == "app":
            _first_order(head["arg"], visited)
            head = head["fn"]
        if head["kind"] != "const":
            raise UnsupportedExpression("higher-order or variable-headed application")
        return
    if kind == "proj":
        _first_order(expr["struct"], visited)
        return
    raise UnsupportedExpression(f"nonidentical {kind} is outside first-order matching")


def _substitute(expr: Any, substitutions: Mapping[str, Expr], memo: dict | None = None) -> Any:
    memo = {} if memo is None else memo
    if isinstance(expr, (dict, list)) and id(expr) in memo:
        return memo[id(expr)]
    if isinstance(expr, dict):
        if expr.get("kind") == "fvar" and expr["id"] in substitutions:
            return substitutions[expr["id"]]
        result = {key: _substitute(value, substitutions, memo) for key, value in expr.items()}
        memo[id(expr)] = result
        return result
    if isinstance(expr, list):
        result = [_substitute(value, substitutions, memo) for value in expr]
        memo[id(expr)] = result
        return result
    return expr


def _known_type(expr: Expr, context: Sequence[Expr]) -> Expr | None:
    if expr["kind"] == "fvar":
        return next((b["type_expr"] for b in context if b["id"] == expr["id"]), None)
    if expr["kind"] == "lit":
        return {"kind": "const", "name": "Nat" if expr["literal_kind"] == "nat" else "String",
                "levels": []}
    # This module deliberately does not implement Lean type inference.
    return None


def _context_obligations(left: Sequence[Expr], right: Sequence[Expr],
                         substitutions: Mapping[str, Expr]) -> list[Expr]:
    obligations = []
    if [(b["binder_mode"], b["role"]) for b in left] != [
            (b["binder_mode"], b["role"]) for b in right]:
        obligations.append({"kind": "telescope", "status": "unresolved",
                            "reason": "ordered binder modes or roles differ"})
    for index, binder in enumerate(left):
        if binder["role"] == "object" and index < len(right):
            expected = _substitute(binder["type_expr"], substitutions)
            actual = right[index]["type_expr"]
            if not _same(expected, actual):
                obligations.append({"kind": "object_context_type", "status": "unresolved",
                                    "binder": binder["id"], "expected": expected, "actual": actual})
    conditions = [b for b in right if b["role"] == "condition"]
    for index, binder in enumerate(b for b in left if b["role"] == "condition"):
        expected = _substitute(binder["type_expr"], substitutions)
        actual = conditions[index]["type_expr"] if index < len(conditions) else None
        if not _same(expected, actual):
            obligations.append({"kind": "condition", "status": "unresolved",
                                "binder": binder["id"], "expected": expected, "actual": actual})
    return obligations


def align_objects(pattern: Mapping[str, Any], target: Mapping[str, Any], *,
                  pattern_binders: Sequence[Mapping[str, Any]] = (),
                  target_binders: Sequence[Mapping[str, Any]] = (),
                  max_nodes: int = 10000) -> Expr:
    """Match first-order object variables, returning substitutions and obligations.

    Substitution expressions use normalized context IDs ``b0``, ``b1``, ... .
    Condition binders and constant function symbols are rigid. ``compatible``
    means syntactic matching with known matching types, not a checked Lean term.
    """
    try:
        a = alpha_normalize(pattern, pattern_binders, max_nodes=max_nodes)
        b = alpha_normalize(target, target_binders, max_nodes=max_nodes)
        digest_memo: dict = {}
        if _same(a, b, digest_memo):
            return {"status": "exact", "substitutions": [], "obligations": []}
        _first_order(a["expr"])
        _first_order(b["expr"])
        variables = {item["id"]: item for item in a["ordered_telescope"]
                     if item["role"] == "object"}
        substitutions: dict[str, Expr] = {}
        matched: set[tuple[int, int]] = set()

        def match(x: Expr, y: Expr) -> bool:
            pair = (id(x), id(y))
            if pair in matched:
                return True
            if x["kind"] == "fvar" and x["id"] in variables:
                if variables[x["id"]]["type_expr"]["kind"] == "forallE":
                    raise UnsupportedExpression("function-typed object variable")
                previous = substitutions.setdefault(x["id"], y)
                return _same(previous, y, digest_memo)
            if x["kind"] != y["kind"]:
                return False
            if x["kind"] == "app":
                result = match(x["fn"], y["fn"]) and match(x["arg"], y["arg"])
                if result:
                    matched.add(pair)
                return result
            if x["kind"] == "proj":
                return x["type_name"] == y["type_name"] and x["index"] == y["index"] and \
                    match(x["struct"], y["struct"])
            return _same(x, y, digest_memo)

        if not match(a["expr"], b["expr"]):
            return {"status": "incompatible", "reason": "rigid syntax or repeated variable differs",
                    "substitutions": [], "obligations": []}
        obligations = _context_obligations(a["ordered_telescope"], b["ordered_telescope"],
                                           substitutions)
        output = []
        for variable, value in substitutions.items():
            expected = _substitute(variables[variable]["type_expr"], substitutions)
            actual = _known_type(value, b["ordered_telescope"])
            if actual is not None and not _same(expected, actual, digest_memo):
                return _pack_result({"status": "incompatible", "reason": "object substitution type differs",
                        "object": variable, "expected": expected, "actual": actual,
                        "substitutions": output, "obligations": obligations})
            if actual is None:
                obligations.append({"kind": "type", "status": "unresolved", "object": variable,
                                    "expected": expected, "target_expr": value})
            output.append({"object": variable, "source_id": pattern_binders[int(variable[1:])]["id"],
                           "target_expr": value, "expected_type": expected, "target_type": actual})
        return _pack_result({"status": "unverified" if obligations else "compatible",
                "substitutions": output, "obligations": obligations,
                "normalization": "ordered telescope IDs"})
    except UnsupportedExpression as exc:
        return {"status": "unsupported", "reason": str(exc), "substitutions": [], "obligations": []}


def anti_unify(left: Mapping[str, Any], right: Mapping[str, Any], *,
               left_binders: Sequence[Mapping[str, Any]] = (),
               right_binders: Sequence[Mapping[str, Any]] = (),
               max_nodes: int = 10000) -> Expr:
    """Find a bounded common first-order shape with typed object/literal holes.

    Rigid function symbols must agree; this intentionally does not generalize
    arbitrary subtrees or different constants to unrestricted wildcards.
    Returned ``hole`` nodes describe a candidate pattern, not Lean expressions.
    """
    try:
        a = alpha_normalize(left, left_binders, max_nodes=max_nodes)
        b = alpha_normalize(right, right_binders, max_nodes=max_nodes)
        digest_memo: dict = {}
        if _same(a, b, digest_memo):
            return _pack_result({"status": "exact", "pattern": a["expr"],
                                 "substitutions": [], "obligations": []})
        _first_order(a["expr"])
        _first_order(b["expr"])
        holes: dict[str, Expr] = {}
        obligations = _context_obligations(a["ordered_telescope"], b["ordered_telescope"], {})
        objects_a = {item["id"] for item in a["ordered_telescope"] if item["role"] == "object"}
        objects_b = {item["id"] for item in b["ordered_telescope"] if item["role"] == "object"}
        generalized: dict[tuple[int, int], Expr] = {}

        def generalize(x: Expr, y: Expr) -> Expr:
            pair_id = (id(x), id(y))
            if pair_id in generalized:
                return generalized[pair_id]
            tx, ty = _known_type(x, a["ordered_telescope"]), _known_type(y, b["ordered_telescope"])
            if tx is not None and ty is not None and not _same(tx, ty, digest_memo):
                raise ValueError("disagreement terms have different types")
            if _same(x, y, digest_memo):
                generalized[pair_id] = x
                return x
            if x["kind"] == y["kind"] == "app":
                result = {"kind": "app", "fn": generalize(x["fn"], y["fn"]),
                        "arg": generalize(x["arg"], y["arg"])}
                generalized[pair_id] = result
                return result
            if x["kind"] == y["kind"] == "proj" and \
                    (x["type_name"], x["index"]) == (y["type_name"], y["index"]):
                return {"kind": "proj", "type_name": x["type_name"], "index": x["index"],
                        "struct": generalize(x["struct"], y["struct"])}
            if x["kind"] not in {"fvar", "lit"} and y["kind"] not in {"fvar", "lit"}:
                raise ValueError("different rigid constants or function symbols")
            if (x["kind"] == "fvar" and x["id"] not in objects_a) or \
                    (y["kind"] == "fvar" and y["id"] not in objects_b):
                raise ValueError("condition variables are rigid")
            if any(t is not None and t["kind"] == "forallE" for t in (tx, ty)):
                raise UnsupportedExpression("function-typed disagreement")
            pair = _syntax_digest(x, digest_memo) + ":" + _syntax_digest(y, digest_memo)
            if pair not in holes:
                hole = {"hole": f"H{len(holes)}", "left": x, "right": y, "type_expr": tx or ty}
                holes[pair] = hole
                if tx is None or ty is None:
                    obligations.append({"kind": "type", "status": "unresolved", **hole})
            result = {"kind": "hole", "id": holes[pair]["hole"], "type_expr": tx or ty}
            generalized[pair_id] = result
            return result

        pattern = generalize(a["expr"], b["expr"])
        return _pack_result({"status": "unverified" if obligations else "compatible", "pattern": pattern,
                "substitutions": list(holes.values()), "obligations": obligations,
                "normalization": "ordered telescope IDs"})
    except UnsupportedExpression as exc:
        return {"status": "unsupported", "reason": str(exc), "substitutions": [], "obligations": []}
    except ValueError as exc:
        return {"status": "incompatible", "reason": str(exc), "substitutions": [], "obligations": []}


def exact_clusters(records: Iterable[Mapping[str, Any]], field: str = "type_expr",
                   binders_field: str = "ordered_telescope", *, max_nodes: int = 10000) -> Expr:
    """Inventory exact syntax duplicates, reporting missing/unsupported records.

    For proof duplication pass the exported proof-expression field explicitly;
    proof terms are never compared using definitional equality. A structure's
    declaration type alone is not its field telescope: export/choose that field
    expression to inventory duplicate structures.
    """
    groups: dict[str, list[Expr]] = defaultdict(list)
    skipped = []
    for index, record in enumerate(records):
        identity = {"index": index, "name": record.get("name", record.get("declaration")),
                    "path": record.get("path", record.get("file"))}
        value: Any = record
        for part in field.split("."):
            value = value.get(part) if isinstance(value, Mapping) else None
        if not isinstance(value, Mapping):
            skipped.append({**identity, "reason": f"missing expression field: {field}"})
            continue
        try:
            fingerprint = alpha_fingerprint(value, record.get(binders_field, ()),
                                            record.get("universe_params", ()), max_nodes=max_nodes)
            groups[fingerprint].append(identity)
        except UnsupportedExpression as exc:
            skipped.append({**identity, "reason": str(exc)})
    return {"comparison": "alpha-normalized syntax", "field": field,
            "clusters": [{"status": "exact", "fingerprint": fingerprint, "members": members}
                         for fingerprint, members in sorted(groups.items()) if len(members) > 1],
            "skipped": skipped}


def exact_structure_clusters(records: Iterable[Mapping[str, Any]], fields_field: str = "fields",
                             parameters_field: str = "ordered_telescope", *,
                             max_nodes: int = 10000) -> Expr:
    """Group explicitly exported field telescopes, independently of record names.

    Fields must use the same ordered binder schema as parameters. Their types,
    modes, dependencies and let values are retained; only printed field names
    are ignored. Missing field exports are skipped, never guessed from text.
    """
    transformed = []
    for record in records:
        item = dict(record)
        fields = item.get(fields_field)
        if isinstance(fields, list):
            context = [*item.get(parameters_field, ()), *fields]
            # Exported field indices may be local to the field telescope.
            context = [{**binder, "index": index} for index, binder in enumerate(context)]
            item["_structure_context"] = context
            item["_structure_shape"] = {"kind": "sort", "level": {"kind": "zero"}}
        transformed.append(item)
    result = exact_clusters(transformed, "_structure_shape", "_structure_context",
                            max_nodes=max_nodes)
    result["field"] = fields_field
    return result


def _target_change(left: Mapping[str, Any], right: Mapping[str, Any],
                   old_context: Sequence[Expr], new_context: Sequence[Expr]) -> Expr:
    """Compare target syntax separately from added/removed context entries."""
    try:
        a = alpha_normalize(left, old_context)["expr"]
        b = alpha_normalize(right, new_context)["expr"]
        # Align stable local IDs before comparing normalized expressions. This
        # prevents inserting a hypothesis from looking like a changed target.
        old_positions = {item.get("fvar_id", item["id"]): index
                         for index, item in enumerate(old_context)}
        remap = {}
        for index, item in enumerate(new_context):
            identity = item.get("fvar_id", item["id"])
            remap[f"b{index}"] = {"kind": "fvar", "id": f"old{old_positions[identity]}"
                                   if identity in old_positions else f"new{index}"}
        old_map = {f"b{index}": {"kind": "fvar", "id": f"old{index}"}
                   for index in range(len(old_context))}
        return {"status": "exact" if _same(_substitute(a, old_map), _substitute(b, remap))
                else "unverified", "comparison": "target syntax with stable local IDs"}
    except UnsupportedExpression as exc:
        return {"status": "unsupported", "reason": str(exc)}


def step_effect(before: Sequence[Mapping[str, Any]] | Mapping[str, Any],
                after: Sequence[Mapping[str, Any]] | None = None) -> Expr:
    """Describe observed goal/context changes, without attributing tactic semantics.

    Accept either two goal arrays or a trace containing ``goals_before`` and
    ``goals_after``. Goal IDs distinguish new subgoals from target replacement;
    printed text changes alone never establish a proof transformation.
    """
    assignments = []
    if after is None:
        if not isinstance(before, Mapping):
            raise ValueError("a trace record or both goal arrays are required")
        assignments = before.get("goal_assignments_after", [])
        before, after = before.get("goals_before", []), before.get("goals_after", [])
    old = {g.get("scope", g["id"]): g for g in before}
    new = {g.get("scope", g["id"]): g for g in after}
    removed, created = [key for key in old if key not in new], [key for key in new if key not in old]
    effects: Expr = {"removed_goals": removed, "solved_goals": removed if not created else [],
                     "new_goals": created,
                     "persisting_goals": [], "status": "observed"}
    if removed and created:
        effects["goal_replacement"] = {"removed": removed, "created": created,
                                       "parentage": "unverified"}
    effects["goal_dependencies"] = [
        {"goal_id": item["goal_id"], "referenced_goal_ids": item["referenced_goal_ids"]}
        for item in assignments if item.get("assigned") and "referenced_goal_ids" in item]
    for goal_id in (key for key in old if key in new):
        x, y = old[goal_id], new[goal_id]
        hx, hy = x.get("hypotheses", []), y.get("hypotheses", [])
        dx = {h.get("fvar_id", h["id"]): h for h in hx}
        dy = {h.get("fvar_id", h["id"]): h for h in hy}
        changes = {"id": goal_id,
                   "hypotheses_added": [h for h in hy if h.get("fvar_id", h["id"]) not in dx],
                   "hypotheses_removed": [h for h in hx if h.get("fvar_id", h["id"]) not in dy],
                   "hypotheses_changed": []}
        for key in (key for key in dx if key in dy):
            i, j = hx.index(dx[key]), hy.index(dy[key])
            comparison = _target_change(dx[key]["type_expr"], dy[key]["type_expr"], hx[:i], hy[:j])
            fields = [field for field in ("role", "binder_mode", "is_let")
                      if dx[key].get(field) != dy[key].get(field)]
            vx, vy = dx[key].get("value_expr"), dy[key].get("value_expr")
            if vx is not None and vy is not None:
                value_change = _target_change(vx, vy, hx[:i], hy[:j])
                if value_change["status"] != "exact":
                    fields.append("value_expr")
            elif vx != vy:
                fields.append("value_expr")
            if comparison["status"] != "exact" or fields:
                changes["hypotheses_changed"].append({"id": key, "comparison": comparison,
                                                     "fields_changed": fields})
        changes["target"] = _target_change(x["target_expr"], y["target_expr"], hx, hy)
        effects["persisting_goals"].append(changes)
    effects["subgoal_count_change"] = len(new) - len(old)
    return effects
