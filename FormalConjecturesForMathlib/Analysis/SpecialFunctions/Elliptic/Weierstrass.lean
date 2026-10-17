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

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import FormalConjecturesForMathlib.Analysis.Normed.Module.Discrete

/-!
# The real and imaginary periods of a period lattice

`IsRealPeriod Λ Ω` says that the real elements of the lattice `Λ ⊆ ℂ` are exactly the integer
multiples of `Ω`, and `IsImagPeriod Λ Ω` says the same of the purely imaginary ones. For a
`PeriodPair` such periods exist unconditionally (`PeriodPair.realPeriod`,
`PeriodPair.imagPeriod`), by `AddSubgroup.exists_inf_span_eq_zmultiples`; they are nonzero when
the lattice is stable under complex conjugation (`PeriodPair.realPeriod_ne_zero`,
`PeriodPair.imagPeriod_ne_zero`).
-/

@[expose] public section

open Complex ComplexConjugate

namespace PeriodPair

/-- `L` uniformises the Weierstrass model `y² = 4x³ - g₂ x - g₃` when its lattice invariants are
`g₂` and `g₃`. -/
def Uniformises (L : PeriodPair) (g₂ g₃ : ℚ) : Prop := L.g₂ = g₂ ∧ L.g₃ = g₃

end PeriodPair

/-- `Ω` is a real period of the lattice `Λ`: the real elements of `Λ` are exactly the integer
multiples of `Ω`. -/
def IsRealPeriod (Λ : Submodule ℤ ℂ) (Ω : ℂ) : Prop :=
  Λ.toAddSubgroup ⊓ (ℝ ∙ (1 : ℂ)).toAddSubgroup = AddSubgroup.zmultiples Ω

/-- `Ω` is an imaginary period of the lattice `Λ`: the purely imaginary elements of `Λ` are
exactly the integer multiples of `Ω`. -/
def IsImagPeriod (Λ : Submodule ℤ ℂ) (Ω : ℂ) : Prop :=
  Λ.toAddSubgroup ⊓ (ℝ ∙ I).toAddSubgroup = AddSubgroup.zmultiples Ω

variable {Λ : Submodule ℤ ℂ} {Ω : ℂ}

theorem IsRealPeriod.mem (h : IsRealPeriod Λ Ω) : Ω ∈ Λ := (h ▸ AddSubgroup.mem_zmultiples _).1

theorem IsImagPeriod.mem (h : IsImagPeriod Λ Ω) : Ω ∈ Λ := (h ▸ AddSubgroup.mem_zmultiples _).1

namespace PeriodPair

variable (L : PeriodPair)

instance : DiscreteTopology L.lattice.toAddSubgroup :=
  inferInstanceAs (DiscreteTopology L.lattice)

theorem exists_isRealPeriod : ∃ Ω, IsRealPeriod L.lattice Ω :=
  L.lattice.toAddSubgroup.exists_inf_span_eq_zmultiples one_ne_zero

theorem exists_isImagPeriod : ∃ Ω, IsImagPeriod L.lattice Ω :=
  L.lattice.toAddSubgroup.exists_inf_span_eq_zmultiples I_ne_zero

/-- A generator of the subgroup of real elements of the lattice of `L`. -/
noncomputable def realPeriod : ℂ := L.exists_isRealPeriod.choose

/-- A generator of the subgroup of purely imaginary elements of the lattice of `L`. -/
noncomputable def imagPeriod : ℂ := L.exists_isImagPeriod.choose

theorem isRealPeriod_realPeriod : IsRealPeriod L.lattice L.realPeriod :=
  L.exists_isRealPeriod.choose_spec

theorem isImagPeriod_imagPeriod : IsImagPeriod L.lattice L.imagPeriod :=
  L.exists_isImagPeriod.choose_spec

/-- The two periods of a `PeriodPair` are `ℝ`-independent, so its lattice is not contained in
any real line. -/
theorem exists_mem_lattice_forall_ne_mul (v : ℂ) : ∃ z ∈ L.lattice, ∀ t : ℝ, z ≠ t * v := by
  by_contra! hline
  obtain ⟨t₁, h₁⟩ := hline L.ω₁ L.ω₁_mem_lattice
  obtain ⟨t₂, h₂⟩ := hline L.ω₂ L.ω₂_mem_lattice
  obtain ⟨-, e₂⟩ := LinearIndependent.pair_iff.mp L.indep t₂ (-t₁)
    (by rw [h₁, h₂]; simp only [Complex.real_smul]; push_cast; ring)
  exact L.indep.ne_zero 0 (by simp [h₁, neg_eq_zero.mp e₂])

end PeriodPair

theorem IsRealPeriod.ne_zero {L : PeriodPair} (h : IsRealPeriod L.lattice Ω)
    (hconj : ∀ z ∈ L.lattice, conj z ∈ L.lattice) : Ω ≠ 0 := by
  rintro rfl
  obtain ⟨z, hz, hne⟩ := L.exists_mem_lattice_forall_ne_mul I
  refine hne z.im ?_
  have hmem : z + conj z ∈ L.lattice.toAddSubgroup ⊓ (ℝ ∙ (1 : ℂ)).toAddSubgroup :=
    AddSubgroup.mem_inf.mpr ⟨add_mem hz (hconj z hz), Submodule.mem_span_singleton.mpr
      ⟨2 * z.re, by rw [Complex.add_conj, Complex.real_smul, mul_one]⟩⟩
  rw [h, AddSubgroup.zmultiples_zero_eq_bot] at hmem
  have hre : z.re = 0 := by
    have hz₀ := Complex.add_conj _ ▸ AddSubgroup.mem_bot.mp hmem
    simpa using hz₀
  exact Complex.ext (by simpa using hre) (by simp)

theorem IsImagPeriod.ne_zero {L : PeriodPair} (h : IsImagPeriod L.lattice Ω)
    (hconj : ∀ z ∈ L.lattice, conj z ∈ L.lattice) : Ω ≠ 0 := by
  rintro rfl
  obtain ⟨z, hz, hne⟩ := L.exists_mem_lattice_forall_ne_mul 1
  refine hne z.re ?_
  have hmem : z - conj z ∈ L.lattice.toAddSubgroup ⊓ (ℝ ∙ I).toAddSubgroup :=
    AddSubgroup.mem_inf.mpr ⟨sub_mem hz (hconj z hz), Submodule.mem_span_singleton.mpr
      ⟨2 * z.im, by rw [Complex.sub_conj, Complex.real_smul]⟩⟩
  rw [h, AddSubgroup.zmultiples_zero_eq_bot] at hmem
  have him : z.im = 0 := by
    have hz₀ := Complex.sub_conj _ ▸ AddSubgroup.mem_bot.mp hmem
    simpa using hz₀
  exact Complex.ext (by simp) (by simpa using him)

namespace PeriodPair

theorem realPeriod_ne_zero {L : PeriodPair}
    (hconj : ∀ z ∈ L.lattice, conj z ∈ L.lattice) : L.realPeriod ≠ 0 :=
  L.isRealPeriod_realPeriod.ne_zero hconj

theorem imagPeriod_ne_zero {L : PeriodPair}
    (hconj : ∀ z ∈ L.lattice, conj z ∈ L.lattice) : L.imagPeriod ≠ 0 :=
  L.isImagPeriod_imagPeriod.ne_zero hconj

end PeriodPair
