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

public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tensor rank

The tensor rank of an element `x : ⨂[R] i, s i` is the least number of pure tensors
`tprod R f = ⨂ₜ[R] i, f i` whose sum is `x`.
-/

@[expose] public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R] {ι : Type*} {s : ι → Type*}
  [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

/-- The tensor rank of `x : ⨂[R] i, s i`: the least `r` such that `x` is the sum of `r` pure
tensors `tprod R f`. Every tensor is a finite sum of pure tensors, so the infimum is attained;
see `PiTensorProduct.exists_eq_sum_tprod`. -/
noncomputable def tensorRank (x : ⨂[R] i, s i) : ℕ :=
  sInf {r | ∃ f : Fin r → ∀ i, s i, x = ∑ j, tprod R (f j)}

theorem tensorRank_sum_tprod_le {τ : Type*} [Fintype τ] (f : τ → ∀ i, s i) :
    tensorRank (∑ t, tprod R (f t)) ≤ Fintype.card τ :=
  Nat.sInf_le ⟨fun j ↦ f ((Fintype.equivFin τ).symm j),
    (Equiv.sum_comp (Fintype.equivFin τ).symm fun t ↦ tprod R (f t)).symm⟩

@[simp]
theorem tensorRank_zero : tensorRank (0 : ⨂[R] i, s i) = 0 := by
  simpa using tensorRank_sum_tprod_le (R := R) (s := s) (τ := Empty) fun e ↦ e.elim

theorem tensorRank_tprod_le (f : ∀ i, s i) : tensorRank (tprod R f) ≤ 1 := by
  have h := tensorRank_sum_tprod_le (R := R) (τ := Unit) fun _ ↦ f
  rwa [Finset.univ_unique, Finset.sum_singleton, Fintype.card_unique] at h

/-- Every tensor is a finite sum of pure tensors. -/
theorem exists_eq_sum_tprod [Nonempty ι] (x : ⨂[R] i, s i) :
    ∃ (r : ℕ) (f : Fin r → ∀ i, s i), x = ∑ j, tprod R (f j) := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨1, fun _ ↦ Function.update f i₀ (c • f i₀), ?_⟩
    rw [Finset.univ_unique, Finset.sum_singleton, MultilinearMap.map_update_smul,
      Function.update_eq_self]
  | add x y hx hy =>
    obtain ⟨r, f, rfl⟩ := hx
    obtain ⟨t, g, rfl⟩ := hy
    refine ⟨r + t, Sum.elim f g ∘ finSumFinEquiv.symm, ?_⟩
    calc ∑ j, tprod R (f j) + ∑ j, tprod R (g j)
        = ∑ u : Fin r ⊕ Fin t, tprod R (Sum.elim f g u) := by simp [Fintype.sum_sum_type]
      _ = ∑ j, tprod R ((Sum.elim f g ∘ finSumFinEquiv.symm) j) :=
        (Fintype.sum_equiv finSumFinEquiv.symm _ _ fun _ ↦ rfl).symm

theorem tensorRank_add_le [Nonempty ι] (x y : ⨂[R] i, s i) :
    tensorRank (x + y) ≤ tensorRank x + tensorRank y := by
  have hx : {r | ∃ f : Fin r → ∀ i, s i, x = ∑ j, tprod R (f j)}.Nonempty :=
    let ⟨r, f, h⟩ := exists_eq_sum_tprod x; ⟨r, f, h⟩
  have hy : {r | ∃ g : Fin r → ∀ i, s i, y = ∑ j, tprod R (g j)}.Nonempty :=
    let ⟨r, g, h⟩ := exists_eq_sum_tprod y; ⟨r, g, h⟩
  obtain ⟨f, hf⟩ := Nat.sInf_mem hx
  obtain ⟨g, hg⟩ := Nat.sInf_mem hy
  have h := tensorRank_sum_tprod_le (R := R) (Sum.elim f g)
  rw [Fintype.sum_sum_type] at h
  simp only [Sum.elim_inl, Sum.elim_inr, ← hf, ← hg, Fintype.card_sum, Fintype.card_fin] at h
  exact h

end PiTensorProduct
