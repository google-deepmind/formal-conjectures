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
# Erdős Problem 782

*References:*
- [erdosproblems.com/782](https://www.erdosproblems.com/782)
- [BEF90] Brown, T. C. and Erdős, P. and Freedman, A. R., *Quasi-progressions and descending
  waves*. J. Combin. Theory Ser. A (1990), 81-95.
- [So07] Solymosi, József, *Elementary additive combinatorics*. (2007), 29-38.
- [CiGr07] Cilleruelo, Javier and Granville, Andrew, *Lattice points on circles, squares in
  arithmetic progressions and sumsets of squares*. (2007), 241-262.
-/

@[expose] public section

namespace Erdos782

/-- `IsQuasiProgression C d x` means that consecutive terms of $x_1, \ldots, x_k$ satisfy
$x_i + d \leq x_{i+1} \leq x_i + d + C$. -/
def IsQuasiProgression (C d : ℕ) {k : ℕ} (x : Fin k → ℕ) : Prop :=
  ∀ i j : Fin k, (j : ℕ) = i + 1 → x i + d ≤ x j ∧ x j ≤ x i + d + C

/--
Do the squares contain arbitrarily long quasi-progressions? That is, is there a constant $C > 0$
such that, for every $k$, the squares contain a sequence $x_1, \ldots, x_k$ where, for some $d$
and all $1 \leq i < k$, $x_i + d \leq x_{i+1} \leq x_i + d + C$?

A question of Brown, Erdős and Freedman [BEF90]. We require $d \geq 1$. With $d = 0$, a constant
sequence would be a quasi-progression. The squares are integers, so taking $C$ and $d$ to be
natural numbers loses no generality.
-/
@[category research open, AMS 11]
theorem erdos_782.parts.i :
    answer(sorry) ↔ ∃ C > 0, ∀ k, ∃ d ≥ 1, ∃ x : Fin k → ℕ,
      (∀ i, IsSquare (x i)) ∧ IsQuasiProgression C d x := by
  sorry

/--
Do the squares contain arbitrarily large cubes
$a + \{\sum_i \epsilon_i b_i : \epsilon_i \in \{0, 1\}\}$?

A question of Brown, Erdős and Freedman [BEF90]. We require each $b_i \geq 1$. With $b_i = 0$,
the cube would be the single square $a$. Solymosi [So07] conjectured that the answer is no.
Cilleruelo and Granville [CiGr07] observed that the answer is no if the Bombieri-Lang
conjecture holds.
-/
@[category research open, AMS 11]
theorem erdos_782.parts.ii :
    answer(sorry) ↔ ∀ n, ∃ a : ℕ, ∃ b : Fin n → ℕ, (∀ i, 0 < b i) ∧
      ∀ S : Finset (Fin n), IsSquare (a + ∑ i ∈ S, b i) := by
  sorry

end Erdos782
