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
# The Ryser design conjecture

A Ryser design on $v$ points has $v$ blocks, constant intersection size $\lambda$, and at
least two block sizes, all greater than $\lambda$. The Ryser design conjecture asserts that
every such design arises by retaining one block of a symmetric design and taking its symmetric
difference with every other block.

*References:*
* T. D. Parulekar and S. S. Sane,
  [Some results on the Ryser design conjecture](https://doi.org/10.1002/jcd.21699),
  *Journal of Combinatorial Designs* **28** (2020), 349–357, Definitions 1.1–1.2.
* [Author's text](https://arxiv.org/html/1907.12482v3)
-/

@[expose] public section

namespace Arxiv.«1907.12482»

open scoped symmDiff

/-- A symmetric $(v,k,\lambda)$ design, specified by its blocks on $v$ points. -/
def IsSymmetricDesign {v : ℕ} (k lam : ℕ) (D : Finset (Finset (Fin v))) : Prop :=
  0 < lam ∧ lam < k ∧ D.card = v ∧
    (∀ B ∈ D, B.card = k) ∧
    ∀ B ∈ D, ∀ C ∈ D, B ≠ C → (B ∩ C).card = lam

/-- A Ryser design has constant block intersections and nonconstant block sizes. -/
def IsRyserDesign {v : ℕ} (lam : ℕ) (D : Finset (Finset (Fin v))) : Prop :=
  0 < lam ∧ D.card = v ∧ (∀ B ∈ D, lam < B.card) ∧
    (∀ B ∈ D, ∀ C ∈ D, B ≠ C → (B ∩ C).card = lam) ∧
    ∃ B ∈ D, ∃ C ∈ D, B.card ≠ C.card

instance {v : ℕ} (k lam : ℕ) (D : Finset (Finset (Fin v))) :
    Decidable (IsSymmetricDesign k lam D) := by
  unfold IsSymmetricDesign
  infer_instance

instance {v : ℕ} (lam : ℕ) (D : Finset (Finset (Fin v))) :
    Decidable (IsRyserDesign lam D) := by
  unfold IsRyserDesign
  infer_instance

/-- Retain $A$ and replace each other block $B$ by $A\mathbin{\triangle}B$. -/
def complementAt {v : ℕ} (D : Finset (Finset (Fin v))) (A : Finset (Fin v)) :
    Finset (Finset (Fin v)) :=
  D.image fun B => if B = A then A else A ∆ B

/-- Complementing at a suitable block produces a symmetric design. -/
def IsTypeOne {v : ℕ} (D : Finset (Finset (Fin v))) : Prop :=
  ∃ A ∈ D, ∃ k lam : ℕ, IsSymmetricDesign k lam (complementAt D A)

/-- The seven lines of the Fano plane in a cyclic labeling. -/
def fanoLines : Finset (Finset (Fin 7)) :=
  {{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {4, 5, 0}, {5, 6, 1}, {6, 0, 2}}

/-- A chosen line of the Fano plane. -/
def fanoBase : Finset (Fin 7) := {0, 1, 3}

/-- The Ryser design obtained by complementing the Fano plane at a line. -/
def fanoRyser : Finset (Finset (Fin 7)) := complementAt fanoLines fanoBase

set_option maxRecDepth 10000 in
@[category test, AMS 5 51]
theorem fano_is_symmetric : IsSymmetricDesign 3 1 fanoLines := by decide

set_option maxRecDepth 10000 in
@[category test, AMS 5 51]
theorem fano_complement_is_ryser : IsRyserDesign 2 fanoRyser := by decide

set_option maxRecDepth 10000 in
@[category test, AMS 5 51]
theorem fano_complement_is_type_one : IsTypeOne fanoRyser := by
  refine ⟨fanoBase, by decide, 3, 1, ?_⟩
  decide

set_option maxRecDepth 10000 in
@[category test, AMS 5 51]
theorem uniform_fano_not_ryser : ¬ IsRyserDesign 1 fanoLines := by decide

@[category test, AMS 5 51]
theorem index_zero_not_ryser {v : ℕ} (D : Finset (Finset (Fin v))) :
    ¬ IsRyserDesign 0 D := by
  simp [IsRyserDesign]

@[category test, AMS 5 51]
theorem empty_not_ryser (lam : ℕ) :
    ¬ IsRyserDesign (v := 0) lam ∅ := by
  simp [IsRyserDesign]

/-- Complementing the displayed design a second time returns the Fano plane. -/
@[category test, AMS 5 51]
theorem fano_complement_involutive : complementAt fanoRyser fanoBase = fanoLines := by decide

/-- Every Ryser design is of Type-1. -/
@[category research open, AMS 5 51]
theorem every_ryser_design_type_one :
    ∀ (v lam : ℕ) (D : Finset (Finset (Fin v))), IsRyserDesign lam D → IsTypeOne D := by
  sorry

end Arxiv.«1907.12482»
