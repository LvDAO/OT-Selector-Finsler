import unittest

import numpy as np

from tools.proof_atlas.pattern_search import search_patterns


class PatternsTests(unittest.TestCase):
    def test_patterns_are_retrieved_as_executable_contracts(self):
        result = search_patterns("strict contraction nonnegative defect real")
        first = result["lexical"][0]
        self.assertEqual(first["id"], "nonnegative-real-strict-contraction-zero")
        self.assertEqual(set(("conditions", "objects", "proof_detail")) - first["pattern"].keys(), set())
        self.assertIn("{{defect}}", first["pattern"]["application_template"])
        self.assertEqual(result["semantic"], [])

    def test_semantic_and_lexical_pattern_orderings_remain_separate(self):
        class Client:
            def embed_texts(self, texts, batch_size):
                self.texts = texts
                # Query matches the second pattern in this controlled model.
                return np.array([[1, 0], [0, 1], [1, 0], [0, 1], [0, 1]], dtype=np.float32)
        result = search_patterns("strict contraction nonnegative defect real", client=Client())
        self.assertEqual(result["lexical"][0]["id"], "nonnegative-real-strict-contraction-zero")
        self.assertEqual(result["semantic"][0]["id"], "eventual-upper-bound-passes-to-limit")
        self.assertEqual(result["semantic"][0]["cosine_similarity"], 1.0)
        self.assertNotIn("score", result)

    def test_query_is_fts_text_not_fts_syntax(self):
        self.assertEqual(search_patterns('" OR () *')['lexical'], [])


if __name__ == "__main__":
    unittest.main()
