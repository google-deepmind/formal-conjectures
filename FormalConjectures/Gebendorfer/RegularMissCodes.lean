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
# Regular miss-codes of degrees two and three

*References:*
- [J. J. Gebendorfer, Exact Extremal Sizes of Regular Miss-Codes of Degrees Two and Three, Theorem 1.2; manuscript and intake](https://github.com/google-deepmind/formal-conjectures/issues/7280)

This author-posed subproblem concerns restricted union closure of miss-codes,
not Frankl's conjecture or the general regular union-closed problem. Upper
bounds and attainment are separate; no default maximum over an empty class.
-/

@[expose] public section
namespace Gebendorfer.RegularMissCodes
open Finset

/-- Distinct nonempty members of size at most $m-2$, constant incidence degree,
and union closure precisely when the union still has eligible size. -/
def IsMissCode (m b : ℕ) (F : Finset (Finset (Fin m))) : Prop :=
  (∀ S ∈ F, S.Nonempty ∧ S.card ≤ m - 2) ∧
  (∀ x : Fin m, (F.filter fun S => x ∈ S).card = b) ∧
  ∀ S ∈ F, ∀ T ∈ F, (S ∪ T).card ≤ m - 2 → S ∪ T ∈ F

/-- The universal degree-two upper bound for all ground-set sizes at least four. -/
@[category research solved, AMS 5]
theorem degree_two_upper (m : ℕ) (hm : 4 ≤ m) (F : Finset (Finset (Fin m)))
    (hF : IsMissCode m 2 F) : F.card ≤ 4 := by
  sorry

/-- The degree-two bound is attained at every ground-set size at least four. -/
@[category research solved, AMS 5]
theorem degree_two_attained (m : ℕ) (hm : 4 ≤ m) :
    ∃ F : Finset (Finset (Fin m)), IsMissCode m 2 F ∧ F.card = 4 := by
  sorry

/-- The universal degree-three upper bound for ground-set sizes at least four. -/
@[category research solved, AMS 5]
theorem degree_three_upper (m : ℕ) (hm : 4 ≤ m) (F : Finset (Finset (Fin m)))
    (hF : IsMissCode m 3 F) : F.card ≤ 6 := by
  sorry

/-- The degree-three bound is attained at every ground-set size at least four. -/
@[category research solved, AMS 5]
theorem degree_three_attained (m : ℕ) (hm : 4 ≤ m) :
    ∃ F : Finset (Finset (Fin m)), IsMissCode m 3 F ∧ F.card = 6 := by
  sorry

/-- Neither degree occurs at ground-set size two or three. -/
@[category research solved, AMS 5]
theorem small_orders (m b : ℕ) (hm : m = 2 ∨ m = 3) (hb : b = 2 ∨ b = 3) :
    ¬ ∃ F : Finset (Finset (Fin m)), IsMissCode m b F := by
  sorry

end Gebendorfer.RegularMissCodes
