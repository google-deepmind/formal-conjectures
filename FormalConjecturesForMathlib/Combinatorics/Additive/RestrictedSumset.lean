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

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Image
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

@[expose] public section

/-!
# Restricted sumsets

This file defines the restricted sumset $S \hat{+} S$ for a finite set $S$.
-/

namespace Finset

variable {α : Type*} [Add α] [DecidableEq α]

/--
The restricted sumset of a set $S$, denoted $S \hat{+} S$, is the set
$\lbrace s_1 + s_2 : s_1, s_2 \in S, s_1 \neq s_2 \rbrace$.
-/
def restrictedSumset (S : Finset α) : Finset α :=
  S.offDiag.image (fun p => p.1 + p.2)

end Finset

namespace Finset

variable {M : Type*} [AddCommMonoid M] [DecidableEq M]

/-- Sums of exactly `r` distinct members of a finite set. -/
def restrictedSums (r : ℕ) (A : Finset M) : Finset M :=
  (A.powersetCard r).image fun B ↦ ∑ a ∈ B, a

/-- The only sum of zero distinct elements is zero. -/
@[simp] theorem restrictedSums_zero (A : Finset M) : restrictedSums 0 A = {0} := by
  simp [restrictedSums]

end Finset

namespace Set

variable {M : Type*} [AddCommMonoid M]

/-- Sums of exactly `r` distinct members of a possibly infinite set. -/
def restrictedSums (r : ℕ) (A : Set M) : Set M :=
  {n | ∃ s : Finset M, (s : Set M) ⊆ A ∧ s.card = r ∧ ∑ a ∈ s, a = n}

/-- Sums of at most `r` distinct members of a possibly infinite set. -/
def restrictedSumsUpTo (A : Set M) (r : ℕ) : Set M :=
  {n | ∃ s : Finset M, (s : Set M) ⊆ A ∧ s.card ≤ r ∧ ∑ a ∈ s, a = n}

/-- The only sum of zero distinct elements is zero. -/
@[simp] theorem restrictedSums_zero (A : Set M) : restrictedSums 0 A = {0} := by
  ext n
  simp [restrictedSums, Finset.card_eq_zero]

end Set

namespace Finset

/-- The finite and set versions count the same distinct-element sums. -/
theorem coe_restrictedSums {M : Type*} [AddCommMonoid M] [DecidableEq M]
    (r : ℕ) (A : Finset M) :
    (restrictedSums r A : Set M) = Set.restrictedSums r A := by
  ext n
  simp only [restrictedSums, Set.restrictedSums, mem_coe, mem_image, mem_powersetCard,
    Set.mem_ofPred_eq, coe_subset]
  aesop

end Finset
