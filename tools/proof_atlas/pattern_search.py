"""First-class retrieval of reusable proof patterns alongside declarations."""

from __future__ import annotations

import json
import re
import sqlite3

from .verify import load_patterns


def _text(pattern):
    return "\n".join((pattern["id"], pattern.get("title", ""),
                      " ".join(pattern.get("tags", [])),
                      json.dumps(pattern["conditions"], ensure_ascii=False),
                      json.dumps(pattern["objects"], ensure_ascii=False),
                      pattern["proof_detail"].get("explanation", "")))


def search_patterns(query: str, *, client=None, limit=4):
    patterns = load_patterns()
    texts = [_text(p) for p in patterns]
    lexical = []
    # Use the same documented lexical method, with no ad-hoc pattern score.
    with sqlite3.connect(":memory:") as db:
        db.execute("CREATE VIRTUAL TABLE p USING fts5(text)")
        db.executemany("INSERT INTO p(rowid,text) VALUES (?,?)", enumerate(texts, 1))
        tokens = re.findall(r"[^\W_]+", query, flags=re.UNICODE)
        expression = " OR ".join('"' + t.replace('"', '""') + '"' for t in tokens)
        if expression:
            lexical = [{"id": patterns[i - 1]["id"], "title": patterns[i - 1].get("title"),
                        "bm25": score, "pattern": patterns[i - 1]}
                       for i, score in db.execute(
                           "SELECT rowid,bm25(p) FROM p WHERE p MATCH ? ORDER BY bm25(p),rowid LIMIT ?",
                           (expression, limit))]
    semantic = []
    if client:
        import numpy as np
        vectors = client.embed_texts([query, *texts], batch_size=5)
        scores = np.asarray(vectors[1:]) @ np.asarray(vectors[0])
        order = np.argsort(-scores, kind="stable")[:limit]
        semantic = [{"id": patterns[int(i)]["id"], "title": patterns[int(i)].get("title"),
                     "cosine_similarity": float(scores[i]), "pattern": patterns[int(i)]}
                    for i in order]
    return {"lexical": lexical, "semantic": semantic}
