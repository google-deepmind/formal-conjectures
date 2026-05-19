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
# Erdős Problem 688
*Reference:*
- [erdosproblems.com/688](https://www.erdosproblems.com/688)
- [Er80] Erdős, Paul, _A survey of problems in combinatorial number theory_. Ann. Discrete Math. (1980), 89-115.
-/

open Classical Real Filter

namespace Erdos688

/--
Define $\epsilon_n$ to be maximal such that there exists some choice of congruence class $a_p$
for all primes $n^{\epsilon_n} < p \leq n$ such that every integer in $[1,n]$ satisfies at least
one of the congruences $\equiv a_p \pmod p$.
-/
def Erdos688Prop (n : ℕ) (ε : ℝ) : Prop :=
  ∃ (a : ℕ → ℕ), ∀ (m : ℕ), 1 ≤ m → m ≤ n →
    ∃ (p : ℕ), p.Prime ∧ (n : ℝ)^ε < p ∧ p ≤ n ∧
      a p ≡ m [MOD p]

noncomputable def epsilonFunction (n : ℕ) : ℝ := sSup {ε : ℝ | Erdos688Prop n ε}

/--
Estimate $\epsilon_n$ - lower bound.
-/
@[category research open, AMS 11]
theorem erdos_688.parts.i.lower_bound :
    (answer(sorry) : ℕ → ℝ) =O[atTop] epsilonFunction := by
  sorry

/--
Estimate $\epsilon_n$ - upper bound.
-/
@[category research open, AMS 11]
theorem erdos_688.parts.i.upper_bound :
    epsilonFunction =O[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
In particular, is it true that $\epsilon_n = o(1)$?
-/
@[category research open, AMS 11]
theorem erdos_688.parts.ii : answer(sorry) ↔
    epsilonFunction =o[atTop] (fun (n : ℕ) ↦ (1 : ℝ)) := by
  sorry

/--
Erdős claims in [Er80] (p. 106) that it is not difficult to prove
$\epsilon_n \gg \frac{\log\log\log n}{\log\log n}$.
-/
@[category research solved, AMS 11]
theorem erdos_688.variants.lglglg_over_lglg_is_big_o :
    (fun (n : ℕ) ↦ (log (log (log (n : ℝ)))) / (log (log (n : ℝ))))
      =O[atTop] epsilonFunction := by
  sorry

end Erdos688
