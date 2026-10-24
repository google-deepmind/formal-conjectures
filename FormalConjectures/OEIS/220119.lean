/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# A double sum of five binomial factors

The sequence is defined by
$a(n)=\sum_{j,k=0}^{n}\binom{n}{j}^2\binom{n}{k}^2\binom{n+j}{n}\binom{n+k}{n}\binom{j+k}{n}$.

*References:*
- [A220119](https://oeis.org/A220119)
- [Li26] Wentao Li, [A proof of the OEIS A220119 conjecture](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/proofs/new-proofs/A220119/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA220119

/-- The double binomial sum defining the sequence. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1),
    ∑ k ∈ Finset.range (n + 1),
      n.choose j ^ 2 * n.choose k ^ 2 * (n + j).choose n * (n + k).choose n * (j + k).choose n

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 12 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 804 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 88680 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 12386340 := by decide

/--
Conjecture 1:
"Conjecture: For $n > 0$, $a(n)$ is always divisible by $(n+1) * (n+2)$."
- F. Chapoton, Apr 23 2026.

The restriction $n > 0$ is necessary since $a(0) = 1$.
Proved and formalized in Lean by Wentao Li, with AI assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/LeanOeisProofs/NewProofs/A220119.lean#L1702"]
theorem conjecture_1 (n : ℕ) (hn : 0 < n) : (n + 1) * (n + 2) ∣ a n := by
  sorry

end OeisA220119
