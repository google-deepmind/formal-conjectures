# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Offline, fail-closed regression tests for exact-head L105 CI construction."""

from pathlib import Path
import re
import unittest

WORKFLOW = (
    Path(__file__).resolve().parents[1]
    / ".github/workflows/rh-krein-l105-coefficient-binding.yml"
)
HEAD_REF = "$" + "{{ env.L105_SOURCE_SHA }}"
HEAD_EXPRESSION = "$" + "{{ github.event.pull_request.head.sha || github.sha }}"
SHARDS = 12
BATCHES = 116


def shard_indices(shard: int) -> tuple[int, ...]:
    if not 0 <= shard < SHARDS:
        raise ValueError("L105_SHARD_OUT_OF_RANGE")
    return tuple(range(shard, BATCHES, SHARDS))


class L105WorkflowContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = WORKFLOW.read_text(encoding="utf-8")

    def test_exact_head_both_event_modes(self):
        s = self.source
        self.assertIn("  push:\n", s)
        self.assertIn("  pull_request:\n", s)
        self.assertIn("      - 'integration/rh-proof-spine-main-root-v1'", s)
        self.assertIn("  L105_SOURCE_SHA: " + HEAD_EXPRESSION, s)
        self.assertEqual(s.count("ref: " + HEAD_REF), 4)
        self.assertNotIn("$GITHUB_SHA", s)
        # Synthetic PR merge commits cannot contaminate artifact identities.
        self.assertEqual(s.count("github.sha"), 1)

    def test_full_job_dependency_graph(self):
        s = self.source.split("\njobs:\n", 1)[1]
        jobs = re.findall(r"(?m)^  ([a-z][a-z0-9-]+):\s*$", s)
        self.assertEqual(
            jobs, ["data-rebind", "kernel-base", "kernel-batches", "kernel-replay"]
        )
        self.assertIn("needs: data-rebind", s)
        self.assertIn("needs: [data-rebind, kernel-base]", s)
        self.assertIn("needs: [data-rebind, kernel-base, kernel-batches]", s)
        self.assertIn("fail-fast: false", s)
        self.assertIn("max-parallel: 4", s)

    def test_shard_partition_is_total_and_disjoint(self):
        self.assertEqual(
            sorted(i for shard in range(SHARDS) for i in shard_indices(shard)),
            list(range(BATCHES)),
        )
        self.assertEqual([len(shard_indices(i)) for i in range(SHARDS)],
                         [10] * 8 + [9] * 4)
        with self.assertRaises(ValueError):
            shard_indices(-1)
        with self.assertRaises(ValueError):
            shard_indices(SHARDS)
        self.assertIn(
            "shard: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]", self.source
        )
        self.assertGreaterEqual(self.source.count("i<116; i+=12"), 3)

    def test_source_and_binary_provenance(self):
        s = self.source
        self.assertIn("L105_GENERATED_HASH_BINDING=119/119", s)
        self.assertIn("L105_SHARD_SOURCE_HASHES=119/119_PASS", s)
        self.assertIn("L105_BATCH_SOURCE_MISMATCH", s)
        self.assertIn("L105_BATCHES=116_OF_116_OLEANS_PRESENT", s)
        self.assertIn("L105_SHARDS=12_OF_12_SHA256_VERIFIED", s)
        self.assertGreaterEqual(s.count("sha256sum -c olean-sha256.txt"), 2)
        self.assertIn("test ! -e \"$OUT/RHKreinL105Batch000.olean\"", s)

    def test_import_path_and_kernel_enforcement(self):
        s = self.source
        self.assertIn('olean="$OUT/$module_path.olean"', s)
        self.assertIn("RHKreinL105Batch[0-9][0-9][0-9]|RHKreinL105AllV1|RHWindowL105FinalV1)", s)
        self.assertIn('lean -o "$OUT/$name.olean" "$GEN/$name.lean"', s)
        self.assertIn('lean -o "$OUT/RHKreinL105AllV1.olean"', s)
        self.assertIn('lean -o "$OUT/RHWindowL105FinalV1.olean"', s)
        self.assertEqual(s.count("#print axioms AEGIS.RHWindowL105FinalV1."), 2)
        self.assertIn("#print axioms AEGIS.RHKreinL105AllV1.zero_quadratic_nonneg_width_21_20", s)
        self.assertIn("test \"$(grep -c 'depends on axioms:' evidence-l105/replay/axioms.log)\" -eq 3", s)
        self.assertIn("! grep -R -n -E 'sorryAx|declaration uses .sorry.|error:'", s)
        final = s.split("\n  kernel-replay:\n", 1)[1]
        self.assertLess(
            final.index("lean /tmp/RHL105Axioms.lean"),
            final.index("L105_BATCH_KERNEL_REPLAY=PASS"),
        )


if __name__ == "__main__":
    unittest.main()
