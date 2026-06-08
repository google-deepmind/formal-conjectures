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
- [A54377](https://oeis.org/A54377) (Primary pseudoperfect numbers)
-/

namespace Erdos313

/--
This set contains all solutions `(m, P)` to the Erdős problem 313.
A solution is a pair where `m` is an integer `≥ 2` and `P` is a non-empty, finite set of
distinct prime numbers, such that the sum of the reciprocals of the primes in `P` equals `1 - 1/m`.
-/
def erdos313Solutions : Set (ℕ × Finset ℕ) :=
  {(m, P) | 2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧ ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m}

/--
Are there infinitely many pairs `(m, P)` where `m ≥ 2` is an integer
and `P` is a set of distinct primes such that the following equation holds:
$\sum_{p \in P} \frac{1}{p} = 1 - \frac{1}{m}$?
-/
@[category research open, AMS 11]
theorem erdos_313 : answer(sorry) ↔ erdos313Solutions.Infinite := by
  sorry

@[category test, AMS 11]
theorem erdos_313.variants.solution_6_2_3 : (6, {2, 3}) ∈ erdos313Solutions := by
  norm_num [erdos313Solutions]

@[category test, AMS 11]
theorem erdos_313.variants.solution_42_2_3_7 : (42, {2, 3, 7}) ∈ erdos313Solutions := by
  norm_num [erdos313Solutions]

/--
An integer `n` is a **primary pseudoperfect number** if it is the denominator `m` in a
solution `(m, P)` to the Erdős 313 problem.
-/
def IsPrimaryPseudoperfect (n : ℕ) : Prop := ∃ P, (n, P) ∈ erdos313Solutions

/--
It is conjectured that the set of primary pseudoperfect numbers is infinite.
-/
@[category research open, AMS 11]
theorem erdos_313.variants.primary_pseudoperfect_are_infinite :
    Set.Infinite {n | IsPrimaryPseudoperfect n} := by
  sorry

/--
There are at least 8 primary pseudoperfect numbers. The first eight terms of
[A54377](https://oeis.org/A54377) are exhibited together with their explicit
prime decompositions.
-/
@[category textbook, AMS 11]
theorem erdos_313.variants.exists_at_least_eight_primary_pseudoperfect :
    8 ≤ (Set.encard {n | IsPrimaryPseudoperfect n}) := by
  let S : Finset ℕ :=
    {2, 6, 42, 1806, 47058, 2214502422, 52495396602,
      8490421583559688410706771261086}
  have hS : (↑S : Set ℕ) ⊆ {n | IsPrimaryPseudoperfect n} := by
    intro x hx
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨{2}, by norm_num [erdos313Solutions]⟩
    · exact ⟨{2, 3}, by norm_num [erdos313Solutions]⟩
    · exact ⟨{2, 3, 7}, by norm_num [erdos313Solutions]⟩
    · exact ⟨{2, 3, 7, 43}, by norm_num [erdos313Solutions]⟩
    · exact ⟨{2, 3, 11, 23, 31}, by norm_num [erdos313Solutions]⟩
    · exact ⟨{2, 3, 11, 23, 31, 47059}, by norm_num [erdos313Solutions]⟩
    · exact ⟨{2, 3, 11, 17, 101, 149, 3109}, by norm_num [erdos313Solutions]⟩
    · exact ⟨{2, 3, 11, 23, 31, 47059, 2217342227, 1729101023519}, by
        refine ⟨by decide, by decide, ?_, ?_⟩
        · intro p hp
          fin_cases hp <;> native_decide
        · native_decide⟩
  calc (8 : ℕ∞)
      = ((S.card : ℕ) : ℕ∞) := by decide
    _ = (↑S : Set ℕ).encard := (Set.encard_coe_eq_coe_finsetCard S).symm
    _ ≤ Set.encard {n | IsPrimaryPseudoperfect n} := Set.encard_le_encard hS

end Erdos313
