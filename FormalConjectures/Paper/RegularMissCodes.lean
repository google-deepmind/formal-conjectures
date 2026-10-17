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
- [J. J. Gebendorfer, Regular union-closed families: a code reduction and the first fifteen rows, July 2026, Definition 4.1 and Section 9, Open Problem 3; public original-source excerpt in the archive](https://github.com/user-attachments/files/33378404/Gebendorfer_MissCodes_Intake_2026-10-13.zip)
- [J. J. Gebendorfer, Exact Extremal Sizes of Regular Miss-Codes of Degrees Two and Three, Theorem 1.2; manuscript archive](https://github.com/user-attachments/files/33378404/Gebendorfer_MissCodes_Intake_2026-10-13.zip)

The July manuscript's Section 9, Open Problem 3, asks for the maximum code
size for degrees two and three at every ground-set size. Definition 4.1 gives
the code conditions. The standalone paper's Theorem 1.2 answers this question:
the maxima are four and six for ground-set sizes at least four, and neither
degree is possible at sizes two or three. This file states that solved problem.

The closure condition is restricted to eligible unions. This is not Frankl's
conjecture or the full regular union-closed problem. Upper bounds and attainment
are stated separately. The linked Lean proofs establish attainment. The small-order exclusion is proved
below. The universal upper bounds still rely on the manuscript's written proof.
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
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/RhudeJJJJ/formal-conjectures/blob/e5cdfb9089efa85734d2b9930e08408409695484/Proofs/RegularMissCodesProof.lean#L202"]
theorem degree_two_attained (m : ℕ) (hm : 4 ≤ m) :
    ∃ F : Finset (Finset (Fin m)), IsMissCode m 2 F ∧ F.card = 4 := by
  sorry

/-- The universal degree-three upper bound for ground-set sizes at least four. -/
@[category research solved, AMS 5]
theorem degree_three_upper (m : ℕ) (hm : 4 ≤ m) (F : Finset (Finset (Fin m)))
    (hF : IsMissCode m 3 F) : F.card ≤ 6 := by
  sorry

/-- The degree-three bound is attained at every ground-set size at least four. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/RhudeJJJJ/formal-conjectures/blob/e5cdfb9089efa85734d2b9930e08408409695484/Proofs/RegularMissCodesProof.lean#L210"]
theorem degree_three_attained (m : ℕ) (hm : 4 ≤ m) :
    ∃ F : Finset (Finset (Fin m)), IsMissCode m 3 F ∧ F.card = 6 := by
  sorry

/-- Neither degree occurs at ground-set size two or three. -/
@[category research solved, AMS 5]
theorem small_orders (m b : ℕ) (hm : m = 2 ∨ m = 3) (hb : b = 2 ∨ b = 3) :
    ¬ ∃ F : Finset (Finset (Fin m)), IsMissCode m b F := by
  rintro ⟨F, hF⟩
  have hm0 : 0 < m := by omega
  let x : Fin m := ⟨0, hm0⟩
  have hsub : F.filter (fun S => x ∈ S) ⊆ {{x}} := by
    intro S hS
    obtain ⟨hSF, hxS⟩ := mem_filter.mp hS
    have hcard : S.card ≤ 1 := by
      have := (hF.1 S hSF).2
      omega
    have heq : S = {x} := by
      symm
      apply eq_of_subset_of_card_le (singleton_subset_iff.mpr hxS)
      simpa using hcard
    simp [heq]
  have hle := card_le_card hsub
  have hb1 : b ≤ 1 := by simpa [hF.2.1 x] using hle
  omega

end Gebendorfer.RegularMissCodes
