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
# Coefficients in a simultaneous approximation to two polylogarithms

Coefficients in a simultaneous approximation to $\operatorname{Li}_2(-1)$ and
$\operatorname{Li}_3(-1)$, given by
$a(n)=\sum_{i,j=0}^{n}\binom{n}{i}^2\binom{n}{j}^2\binom{n+i}{n}\binom{i+j}{i}$.

*References:*
- [A098275](https://oeis.org/A098275)
- [Li26] Wentao Li, [A proof of the OEIS A098275 conjecture](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/proofs/new-proofs/A098275/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA98275

/-- The double binomial sum defining the coefficients. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    n.choose i ^ 2 * n.choose j ^ 2 * (n + i).choose n * (i + j).choose i

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 8 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 264 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 13040 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 778840 := by decide

/--
Conjecture 1:
"Conjecture: $a(n)$ is divisible by $n+1$."
- F. Chapoton, Jan 28 2026.

Proved and formalized in Lean by Wentao Li, with AI assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/LeanOeisProofs/NewProofs/A098275.lean#L166"]
theorem conjecture_1 (n : ℕ) : n + 1 ∣ a n := by
  sorry

end OeisA98275
