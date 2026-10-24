"""Retrieval packets retain conditions, objects, proof steps and source receipts."""

from __future__ import annotations

import re
from typing import Any

from .structure import align_objects, step_effect
from .verify import load_patterns, verify_candidate
from .pattern_search import search_patterns


def _validate_state(state) -> None:
    if not isinstance(state, dict):
        raise ValueError("state must be a JSON object")
    mapping = state.get("object_mapping", {})
    if not isinstance(mapping, dict) or any(not isinstance(key, str) or not isinstance(value, str)
                                             for key, value in mapping.items()):
        raise ValueError("object_mapping must map role names to Lean expression strings")
    for key in ("context", "goal", "query", "candidate", "candidate_kind"):
        if key in state and not isinstance(state[key], str):
            raise ValueError(f"state {key} must be a string")
    if "imports" in state and (not isinstance(state["imports"], list) or
                              any(not isinstance(item, str) for item in state["imports"])):
        raise ValueError("state imports must be a list of module strings")
    if "target_expr" in state and not isinstance(state["target_expr"], dict):
        raise ValueError("state target_expr must be a Lean expression JSON object")
    if "ordered_telescope" in state and (not isinstance(state["ordered_telescope"], list) or
                                        any(not isinstance(item, dict)
                                            for item in state["ordered_telescope"])):
        raise ValueError("state ordered_telescope must be an ordered list of binder objects")


def query_text(state: dict) -> str:
    """A new goal needs no pre-existing proof to enter retrieval."""
    _validate_state(state)
    return "\n".join(str(state.get(key, "")) for key in ("context", "goal", "query"))


def search(store, query: str, *, limit: int = 10, view: str | None = None,
           module: str | None = None, namespace: str | None = None,
           vector_index=None, client=None) -> dict:
    filters = {"view": view, "module": module, "namespace": namespace}
    lexical = store.search_lexical(query, limit=limit, **filters)
    result = {"query": query, "lexical": lexical, "semantic": [],
              "ranking": {"lexical": "SQLite FTS5 BM25", "semantic": "cosine similarity"}}
    if vector_index is not None and client is not None:
        from .vectors import StaleVectorIndex
        try:
            result["semantic"] = vector_index.search(query, client, store, limit=limit, **filters)
        except StaleVectorIndex as exc:
            result["semantic_status"] = {"status": "stale", "reason": str(exc)}
    result["patterns"] = search_patterns(query, client=client, limit=min(limit, 4))
    return result


def _items(lane):
    return lane.get("items", lane.get("results", [])) if isinstance(lane, dict) else lane


def context_packet(store, retrieved: dict, *, state: dict | None = None,
                   limit: int = 8) -> dict:
    if state is not None:
        _validate_state(state)
    references, grouped = [], {}
    # Preserve the two retrieval orderings. No arbitrary fusion score.
    for lane in ("semantic", "lexical"):
        for hit in _items(retrieved.get(lane, [])):
            name = hit.get("declaration", hit.get("name"))
            if not name:
                continue
            grouped.setdefault(name, []).append((lane, hit))
    for name, hits in list(grouped.items())[:max(0, limit)]:
        lane = hits[0][0]
        decl, triad = store.get_decl(name), store.get_triad(name)
        if decl is None:
            raise ValueError(f"retrieved declaration is not indexed: {name}")
        entry = {"declaration": name, "retrieved_by": lane,
                 "retrieval_lanes": list(dict.fromkeys(lane for lane, _ in hits)),
                 "source": {k: decl.get(k) for k in
                            ("module", "source_path", "source_hash", "range")},
                 "conditions": [], "objects": [], "proof_detail": None,
                 "type_dependencies": decl.get("type_dependencies", []),
                 "proof_dependencies": decl.get("proof_dependencies", [])}
        entry["proof_source"] = store.get_proof_text(name)
        if triad:
            binders = triad.get("ordered_telescope", [])
            # Telescope remains authoritative: lists are projections, not reorderings.
            entry.update(ordered_telescope=binders,
                         conditions=[b for b in binders if b.get("role") == "condition"],
                         objects=[b for b in binders if b.get("role") == "object"],
                         goal={"text": (decl.get("type_text") if triad.get("target_text_status") == "unavailable"
                                        else triad.get("target_text")),
                               "text_representation": ("closed_declaration_type" if triad.get("target_text_status") == "unavailable"
                                                       else "open_target"),
                               "expr": triad.get("target_expr")},
                         proof_detail=triad.get("proof_skeleton"))
            if state and state.get("target_expr"):
                entry["structural_match"] = align_objects(
                    triad["target_expr"], state["target_expr"],
                    pattern_binders=binders,
                    target_binders=state.get("ordered_telescope", []))
        fragments, seen_fragments = [], set()
        for _, hit in hits:
            fragment_id = hit.get("metadata", {}).get("fragment_id")
            if fragment_id is None or fragment_id in seen_fragments:
                continue
            seen_fragments.add(fragment_id)
            fragment = store.get_fragment(fragment_id)
            if fragment is None:
                raise ValueError(f"retrieved proof fragment is not indexed: {fragment_id}")
            fragments.append({"fragment": fragment, "step_effect": step_effect(fragment)})
        if fragments:
            entry["fragments"] = fragments
            # Keep the original single-fragment surface for existing callers.
            entry.update(fragments[0])
        references.append(entry)
    snapshot = store.snapshot_status()
    snapshot.pop("manifest", None)
    patterns, seen_patterns = [], set()
    for lane in ("semantic", "lexical"):
        for hit in retrieved.get("patterns", {}).get(lane, []):
            if hit["id"] not in seen_patterns:
                seen_patterns.add(hit["id"])
                patterns.append({"retrieved_by": lane, **hit})
    return {"schema_version": 1, "task": state or {"query": retrieved["query"]},
            "references": references,
            "patterns": patterns,
            "instruction": "Map typed objects, retain missing conditions as obligations, then run Lean. "
                           "Retrieval and syntactic similarity do not certify a transferred proof.",
            "snapshot": snapshot}


def instantiate_pattern(pattern: dict, state: dict) -> dict:
    """Fill only explicit placeholders, without rewriting the user's goal/context."""
    _validate_state(state)
    request = {k: state[k] for k in
               ("imports", "context", "goal", "candidate", "candidate_kind", "object_mapping")
               if k in state}
    mapping = state.get("object_mapping", {})
    template = pattern.get("application_template") or pattern["proof_detail"].get("application_template")
    if "candidate" not in request:
        if not template:
            raise ValueError("pattern requires an explicit candidate; see its verified example")
        missing = sorted(set(re.findall(r"\{\{([\w-]+)\}\}", template)) - mapping.keys())
        if missing:
            raise ValueError("missing explicit object_mapping roles: " + ", ".join(missing))
        request["candidate"] = re.sub(r"\{\{([\w-]+)\}\}",
                                      lambda m: "(" + mapping[m[1]] + ")", template)
    request["remaining_obligations"] = pattern["proof_detail"].get("remaining_obligations", [])
    return request


def transfer(store, state: dict, *, pattern_id: str | None = None,
             declaration: str | None = None, check: bool = False, root=".", timeout=60) -> dict:
    _validate_state(state)
    if pattern_id:
        pattern = next((p for p in load_patterns() if p["id"] == pattern_id), None)
        if pattern is None:
            raise ValueError(f"unknown pattern {pattern_id}")
        request = instantiate_pattern(pattern, state)
        result = {"pattern": pattern_id, "conditions": pattern["conditions"],
                  "objects": pattern["objects"], "proof_detail": pattern["proof_detail"],
                  "request": request, "status": "unverified"}
    elif declaration:
        decl = store.get_decl(declaration)
        if not decl or decl.get("external"):
            raise ValueError("declaration is not indexed; import its module first")
        request = {k: state[k] for k in
                   ("imports", "context", "goal", "candidate", "candidate_kind", "object_mapping")
                   if k in state}
        # Lean elaborates the declaration token; no theorem-name string substitution.
        request.setdefault("candidate", f"apply {declaration}\nall_goals first | assumption | skip")
        result = {"declaration": declaration, "triad": store.get_triad(declaration),
                  "request": request, "status": "unverified"}
        if state.get("target_expr") and result["triad"]:
            triad = result["triad"]
            result["structural_match"] = align_objects(
                triad["target_expr"], state["target_expr"],
                pattern_binders=triad.get("ordered_telescope", []),
                target_binders=state.get("ordered_telescope", []))
    else:
        raise ValueError("select a pattern or an indexed declaration")
    if check:
        result["validation"] = verify_candidate(request, root, timeout_seconds=timeout)
        result["status"] = result["validation"]["status"]
    return result
