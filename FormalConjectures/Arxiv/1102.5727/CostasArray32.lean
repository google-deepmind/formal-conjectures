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
# A Costas array of order 32

A Costas array is a permutation matrix whose displacement vectors between pairs of dots are
all distinct. Such arrays encode frequency-hopping radar and sonar signals. Order $32$ is a
named unresolved case of the existence question.

*References:*
* K. Drakakis, [Open problems in Costas arrays](https://arxiv.org/abs/1102.5727),
  Sections 3.2.3 and 4.1, Problem 1.
* F. Gulec and V. Abolghasemi,
  [Universal Costas Matrices](https://arxiv.org/abs/2602.03407).
* [OEIS A008404](https://oeis.org/A008404).
-/

@[expose] public section

namespace Arxiv.«1102.5727»

/-- The signed displacement vector from dot $i$ to dot $j$ in a permutation array. -/
def displacement {n : ℕ} (f : Equiv.Perm (Fin n)) (i j : Fin n) : ℤ × ℤ :=
  ((j.val : ℤ) - i.val, ((f j).val : ℤ) - (f i).val)

/-- Distinct pairs of dots, ordered by column, have distinct displacement vectors. -/
def IsCostas {n : ℕ} (f : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j k l : Fin n, i < j → k < l →
    displacement f i j = displacement f k l → i = k ∧ j = l

instance {n : ℕ} (f : Equiv.Perm (Fin n)) : Decidable (IsCostas f) := by
  unfold IsCostas
  infer_instance

/-- Reversing a pair of dots negates both coordinates of its displacement. -/
@[category API, AMS 5 94]
theorem displacement_reverse {n : ℕ} (f : Equiv.Perm (Fin n)) (i j : Fin n) :
    displacement f j i = (-(displacement f i j).1, -(displacement f i j).2) := by
  apply Prod.ext <;> dsimp [displacement] <;> omega

/-- The vacuous order-zero case is separate from the positive-order source question. -/
@[category test, AMS 5 94]
theorem empty_permutation_costas : IsCostas (Equiv.refl (Fin 0)) := by
  decide

@[category test, AMS 5 94]
theorem one_dot_costas : IsCostas (Equiv.refl (Fin 1)) := by
  decide

@[category test, AMS 5 94]
theorem two_dot_costas : IsCostas (Equiv.refl (Fin 2)) := by
  decide

/-- The zero-indexed permutation $(0,2,1)$ is a Costas array. -/
@[category test, AMS 5 94]
theorem three_dot_costas : IsCostas (Equiv.swap (1 : Fin 3) 2) := by
  decide

/-- The zero-indexed permutation $(0,1,3,2)$ is a Costas array. -/
@[category test, AMS 5 94]
theorem four_dot_costas : IsCostas (Equiv.swap (2 : Fin 4) 3) := by
  decide

/-- Three collinear equally spaced dots repeat the displacement $(1,1)$. -/
@[category test, AMS 5 94]
theorem three_dot_identity_not_costas : ¬ IsCostas (Equiv.refl (Fin 3)) := by
  decide

/-- The vertical coordinate records negative displacements without natural-number truncation. -/
@[category test, AMS 5 94]
theorem negative_vertical_displacement :
    displacement (Equiv.swap (1 : Fin 3) 2) 1 2 = (1, -1) := by
  decide

/-- Does a Costas array of order $32$ exist? -/
@[category research open, question, AMS 5 94]
theorem costas_array_32 : ∃ f : Equiv.Perm (Fin 32), IsCostas f := by
  sorry

end Arxiv.«1102.5727»
