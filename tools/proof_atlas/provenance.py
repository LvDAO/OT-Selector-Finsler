"""Pure readers for the central mathematical provenance catalog."""

from __future__ import annotations

import json
from pathlib import Path


def load_catalog(path: str | Path) -> dict:
    """Load a catalog without opening the DAG database or modifying any files."""
    with Path(path).open(encoding="utf-8") as source:
        catalog = json.load(source)
    if catalog.get("schema") not in {"mathematical-methods-v4", "mathematical-methods-v5"}:
        raise ValueError("Unsupported mathematical provenance catalog schema")
    return catalog


def resolve_declaration(catalog: dict, declaration_id: str,
                        variant_id: str | None = None) -> dict:
    """Resolve one v5 entry, optionally in an explicitly recorded source view.

    Entry IDs distinguish catalog occurrences; original module/SHA/name/range
    fields retain permanent source identity. Returned dictionaries contain exact
    retained headers, methods, context and ownership, not archived proof bodies.
    Historical private/notation entries do not claim current kernel verification.
    The catalog and its shared tables are left unchanged.
    """
    if catalog.get("schema") != "mathematical-methods-v5":
        raise ValueError("Declaration IDs require a v5 catalog")
    record = dict(catalog["declarations"][declaration_id])
    if variant_id is not None:
        variant = catalog["declaration_variants"][variant_id]
        if variant["declaration_id"] != declaration_id:
            raise ValueError("Source-view variant belongs to another declaration")
        for key in variant["unset"]:
            record.pop(key, None)
        record.update(variant["set"])
    record.pop("id", None)
    record.pop("source_unit_ids", None)
    for field, table in (("method_id", "methods"), ("context_id", "contexts")):
        key = record.pop(field, None)
        if key is not None:
            record.update(catalog[table][key])
    owner = record.pop("owner_id", None)
    if owner is not None:
        record["source_ownership"] = catalog["owners"][owner]
    if record.pop("signature_from_header", False):
        record["signature"] = record["exact_source_header"]
    return record
