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
# Erdős Problem 886

*References:*
- [erdosproblems.com/886](https://www.erdosproblems.com/886)
- [ErRo97] Erdős, Paul and Rosenfeld, Moshe, The factor-difference set of integers. Acta Arith.
  (1997), 353--359.
-/

open Nat Filter

namespace Erdos886

/--
The set of divisors of $n$ in the interval $(n^{1/2}, n^{1/2} + n^{1/2-\epsilon})$.
-/
noncomputable def erdos_886_divisors (n : ℕ) (ε : ℝ) : Finset ℕ :=
  (divisors n).filter (fun d =>
    (n : ℝ) ^ (1/2 : ℝ) < d ∧ (d : ℝ) < (n : ℝ) ^ (1/2 : ℝ) + (n : ℝ) ^ (1/2 - ε))

/--
Let $\epsilon>0$. Is it true that, for all large $n$, the number of divisors of $n$ in
$(n^{1/2},n^{1/2}+n^{1/2-\epsilon})$ is $O_\epsilon(1)$?

Erdős attributes this conjecture to Ruzsa.
-/
@[category research open, AMS 11]
theorem erdos_886 :
    answer(sorry) ↔ ∀ ε > 0, ∃ C : ℕ, ∀ᶠ n in atTop, (erdos_886_divisors n ε).card ≤ C := by
  sorry

/--
Erdős and Rosenfeld [ErRo97] proved that there are infinitely many $n$ such that there are
four divisors of $n$ in $(n^{1/2},n^{1/2}+n^{1/4})$.
-/
@[category research solved, AMS 11]
theorem erdos_886.variants.rosenfeld :
    Set.Infinite {n | 4 ≤ (erdos_886_divisors n (1/4)).card} := by
  sorry

end Erdos886
