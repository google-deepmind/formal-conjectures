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

public import Mathlib.LinearAlgebra.QuadraticForm.Radical

@[expose] public section

/-!
# Dimensions of anisotropic quadratic forms

The *$u$-invariant* $u(F)$ of a field $F$ is the largest dimension of an anisotropic quadratic
form over $F$, or $\infty$ if there is no largest one [Kaplansky1953, p. 201]; in characteristic $2$
the forms are required to be nondegenerate [EKM2008, §36]. This file defines

* `QuadraticForm.anisotropicDims F`: the set of `n` such that there is a nondegenerate anisotropic
  quadratic form on `Fin n → F`.

The $u$-invariant of `F` is `n` exactly when `IsGreatest (QuadraticForm.anisotropicDims F) n`, and
it is infinite exactly when `¬ BddAbove (QuadraticForm.anisotropicDims F)`. No numeric invariant
is defined, so that no convention for the infinite case is needed.

The set contains `0` and `1` for every field. In characteristic not `2` every anisotropic form is
nondegenerate (`QuadraticMap.Anisotropic.nondegenerate`), so the nondegeneracy condition can be
dropped (`QuadraticForm.mem_anisotropicDims_iff`). Over a linearly ordered field the sum of `n`
squares is anisotropic for every `n`, so the set is all of `ℕ`
(`QuadraticForm.anisotropicDims_eq_univ`).

## References

* [Kaplansky1953] I. Kaplansky, *Quadratic forms*, J. Math. Soc. Japan 5 (1953), 200–207.
* [EKM2008] R. Elman, N. Karpenko, A. Merkurjev, *The algebraic and geometric theory of
  quadratic forms*, Amer. Math. Soc. Colloq. Publ. 56, 2008.
-/

open Finset QuadraticMap

namespace QuadraticMap

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M] {Q : QuadraticForm F M}

/-- The radical of an anisotropic quadratic form is trivial. -/
theorem Anisotropic.radical_eq_bot (hQ : Q.Anisotropic) : Q.radical = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun m hm ↦ hQ m (mem_radical_iff'.mp hm).1

/-- An anisotropic quadratic form on a module of rank at most `1` is nondegenerate. -/
theorem Anisotropic.nondegenerate_of_rank_le_one (hQ : Q.Anisotropic)
    (hM : Module.rank F M ≤ 1) : Q.Nondegenerate where
  radical_eq_bot := hQ.radical_eq_bot
  rank_rad_polar_le := (Submodule.rank_le _).trans hM

/-- In characteristic not `2`, an anisotropic quadratic form is nondegenerate. -/
theorem Anisotropic.nondegenerate [NeZero (2 : F)] (hQ : Q.Anisotropic) : Q.Nondegenerate := by
  have := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  exact nondegenerate_iff_radical_eq_bot.mpr hQ.radical_eq_bot

end QuadraticMap

namespace QuadraticForm

variable (F : Type*) [Field F]

/-- The set of `n` such that there is a nondegenerate anisotropic quadratic form on `Fin n → F`.
Its greatest element, when it exists, is the $u$-invariant of `F`; the set is not bounded above
exactly when the $u$-invariant of `F` is infinite. -/
def anisotropicDims : Set ℕ :=
  {n | ∃ Q : QuadraticForm F (Fin n → F), Q.Anisotropic ∧ Q.Nondegenerate}

theorem zero_mem_anisotropicDims : 0 ∈ anisotropicDims F :=
  have h : (0 : QuadraticForm F (Fin 0 → F)).Anisotropic := fun x _ ↦ Subsingleton.elim x 0
  ⟨0, h, h.nondegenerate_of_rank_le_one (by simp)⟩

theorem one_mem_anisotropicDims : 1 ∈ anisotropicDims F :=
  have h : (weightedSumSquares F (1 : Fin 1 → F)).Anisotropic := fun v hv ↦ by
    simp only [weightedSumSquares_apply, Pi.one_apply, one_smul, Fin.sum_univ_one,
      mul_self_eq_zero] at hv
    exact funext fun i ↦ by rw [Fin.fin_one_eq_zero i]; exact hv
  ⟨_, h, h.nondegenerate_of_rank_le_one (by simp)⟩

variable {F}

/-- In characteristic not `2`, the nondegeneracy condition in `anisotropicDims` is automatic. -/
theorem mem_anisotropicDims_iff [NeZero (2 : F)] {n : ℕ} :
    n ∈ anisotropicDims F ↔ ∃ Q : QuadraticForm F (Fin n → F), Q.Anisotropic :=
  ⟨fun ⟨Q, hQ, _⟩ ↦ ⟨Q, hQ⟩, fun ⟨Q, hQ⟩ ↦ ⟨Q, hQ, hQ.nondegenerate⟩⟩

/-- Over a linearly ordered field, the sum of `n` squares is anisotropic for every `n`, so every
`n` is the dimension of an anisotropic quadratic form. -/
theorem anisotropicDims_eq_univ [LinearOrder F] [IsStrictOrderedRing F] :
    anisotropicDims F = Set.univ :=
  Set.eq_univ_of_forall fun n ↦ mem_anisotropicDims_iff.mpr
    ⟨weightedSumSquares F (1 : Fin n → F), fun v hv ↦ by
      simp only [weightedSumSquares_apply, Pi.one_apply, one_smul] at hv
      rw [sum_eq_zero_iff_of_nonneg fun i _ ↦ mul_self_nonneg (v i)] at hv
      exact funext fun i ↦ mul_self_eq_zero.mp (hv i (mem_univ i))⟩

end QuadraticForm
