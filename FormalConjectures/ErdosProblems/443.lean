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

import FormalConjecturesUtil

/-!
# Erdős Problem 443

*References:*
- [erdosproblems.com/443](https://www.erdosproblems.com/443)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [He25] Hegyvári, Norbert, *An elementary question of Erdős and Graham*.
  arXiv:2503.24201 (2025).
-/

namespace Erdos443

/--
The set $\{k(m-k) : 1\leq k\leq m/2\}$, where `m / 2` is `ℕ` floor division.
-/
def A (m : ℕ) : Finset ℕ := (Finset.Icc 1 (m / 2)).image fun k => k * (m - k)

/--
Let $m,n\geq 1$. What is
\[\# \{ k(m-k) : 1\leq k\leq m/2\} \cap \{ l(n-l) : 1\leq l\leq n/2\}?\]
Can it be arbitrarily large? Is it $\leq (mn)^{o(1)}$ for all sufficiently large $m,n$?

This was solved independently by Hegyvári [He25] and Cambie (unpublished), who show that if
$m>n$ then the set in question has size
\[\leq m^{O(1/\log\log m)},\]
and that for any integer $s$ there exist infinitely many pairs $(m,n)$ such that the set in
question has size $s$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos443.lean"]
theorem erdos_443 : answer(True) ↔
    (∀ s : ℕ, ∃ m n : ℕ, n < m ∧ s ≤ (A n ∩ A m).card) ∧
    (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ m n : ℕ, n₀ < n → n < m →
      ((A n ∩ A m).card : ℝ) < ((m : ℝ) * n) ^ ε) := by
  sorry

end Erdos443
