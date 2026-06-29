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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 367

*References:*
- [erdosproblems.com/367](https://www.erdosproblems.com/367)
- [ErGr80] Erdős, P. and Graham, R. L., Old and new problems and results in combinatorial
  number theory. (1980), p. 68.
-/

open Asymptotics Filter

namespace Erdos367

/-- A natural number is powerful if each prime divisor appears to at least the second power. -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- The $2$-full part of `n`, i.e. the largest powerful divisor of `n`. -/
noncomputable def twoFullPart (n : ℕ) : ℕ := by
  classical
  exact if n = 0 then 0 else (n.divisors.filter IsPowerful).max.getD 1

/--
Let $B_2(n)$ be the $2$-full part of $n$ (that is, $B_2(n)=n/n'$ where $n'$ is
the product of all primes that divide $n$ exactly once). Is it true that, for every fixed
$k\geq 1$,
$$\prod_{n\leq m<n+k}B_2(m) \ll n^{2+o(1)}?$$
-/
@[category research open, AMS 11]
theorem erdos_367 : answer(sorry) ↔
    ∀ k ≥ 1, ∀ ε : ℝ, 0 < ε →
      (fun n : ℕ => (∏ m ∈ Finset.Ico n (n + k), (twoFullPart m : ℝ))) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 + ε) := by
  sorry

/--
The stronger question asking whether
$$\prod_{n\leq m<n+k}B_2(m) \ll_k n^2$$
for every fixed $k$ is false. In fact, the bound already fails for $k=3$.
-/
@[category research solved, AMS 11,
formal_proof using lean4 at
"https://github.com/plby/lean-proofs/blob/main/src/v4.30.0/ErdosProblems/Erdos367b.lean#L677"]
theorem erdos_367.variants.quadratic_bound : answer(False) ↔
    ∀ k ≥ 1, ∃ C : ℝ, ∀ n : ℕ,
      (∏ m ∈ Finset.Ico n (n + k), (twoFullPart m : ℝ)) ≤ C * (n : ℝ) * (n : ℝ) := by
  sorry

end Erdos367
