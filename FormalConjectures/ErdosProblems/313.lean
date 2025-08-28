/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 313

*References:*
- [erdosproblems.com/313](https://www.erdosproblems.com/313)
- OEIS: [A054377](https://oeis.org/A054377) (Primary pseudoperfect numbers)
-/

namespace Erdos313

/--
This set contains all solutions `(m, P)` to the Erdős problem 313.
A solution is a pair where `m` is an integer `≥ 2` and `P` is a non-empty, finite set of
distinct prime numbers, such that the sum of the reciprocals of the primes in `P` equals `1 - 1/m`.
-/
def erdos_313_solutions : Set (ℕ × Finset ℕ) :=
  {(m, P) | 2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧ ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m}

/--
Are there infinitely many pairs `(m, P)` where `m ≥ 2` is an integer
and `P` is a set of distinct primes such that the following equation holds:
$\sum_{p \in P} \frac{1}{p} = 1 - \frac{1}{m}$?
-/
@[category research open, AMS 11]
theorem erdos_313_conjecture : erdos_313_solutions.Infinite ↔ answer(sorry) := by
  sorry

@[category test, AMS 11]
theorem erdos_313_solution_6_2_3 : (6, {2, 3}) ∈ erdos_313_solutions := by
  norm_num [erdos_313_solutions]

@[category test, AMS 11]
theorem erdos_313_solution_42_2_3_7 : (42, {2, 3, 7}) ∈ erdos_313_solutions := by
  norm_num [erdos_313_solutions]

/--
An integer `n` is a **primary pseudoperfect number** if it is the denominator `m` in a
solution `(m, P)` to the Erdős 313 problem.
-/
def IsPrimaryPseudoperfect (n : ℕ) : Prop := ∃ P, (n, P) ∈ erdos_313_solutions

/--
It is conjectured that the set of primary pseudoperfect numbers is infinite.
-/
@[category research open, AMS 11]
theorem erdos_313.variant.primary_pseudoperfect_are_infinite :
    Set.Infinite {n | IsPrimaryPseudoperfect n} := by
  sorry

/--
There are at least 8 primary pseudoperfect numbers.
-/
@[category undergraduate, AMS 11]
theorem exists_at_least_eight_primary_pseudoperfect :
    8 ≤ (Set.encard {n | IsPrimaryPseudoperfect n}) := by
  sorry

end Erdos313
