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

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import FormalConjecturesTest.RealPeriod.Uniqueness

/-!
# Real lattices

A period lattice is *real* if it is stable under complex conjugation. The invariants of the
conjugate lattice are the conjugates of the invariants, so a real lattice has real $g_2$ and
$g_3$. Conversely a lattice with real invariants equals its conjugate, because a period lattice
is determined by its invariants: `PeriodPair.isReal_iff_exists_real`.

Ported from the LeanBridge development.
-/

open scoped ComplexConjugate

noncomputable section

namespace PeriodPair

/- ## The conjugate lattice -/

/-- The conjugate period pair, with periods $\overline{\omega_1}$ and $\overline{\omega_2}$; its
lattice is the complex conjugate of $\Lambda$. -/
def conjugate (L : PeriodPair) : PeriodPair where
  ω₁ := conj L.ω₁
  ω₂ := conj L.ω₂
  indep := by
    refine LinearIndependent.pair_iff.mpr fun s t hst =>
      LinearIndependent.pair_iff.mp L.indep s t ?_
    have h := congrArg (starRingEnd ℂ) hst
    simpa [Complex.real_smul] using h

@[simp] lemma conjugate_ω₁ (L : PeriodPair) : L.conjugate.ω₁ = conj L.ω₁ := rfl

@[simp] lemma conjugate_ω₂ (L : PeriodPair) : L.conjugate.ω₂ = conj L.ω₂ := rfl

variable (L : PeriodPair)

lemma mem_conjugate_lattice {x : ℂ} : x ∈ L.conjugate.lattice ↔ conj x ∈ L.lattice := by
  simp only [mem_lattice, conjugate_ω₁, conjugate_ω₂]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp⟩
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, by simpa using congrArg (starRingEnd ℂ) h⟩

/-- Conjugation as a bijection from $\Lambda$ to $\overline{\Lambda}$. -/
def conjugateLatticeEquiv : L.lattice ≃ L.conjugate.lattice where
  toFun l := ⟨conj l, L.mem_conjugate_lattice.mpr (by simp [l.2])⟩
  invFun l' := ⟨conj l', L.mem_conjugate_lattice.mp l'.2⟩
  left_inv l := Subtype.ext (Complex.conj_conj (l : ℂ))
  right_inv l' := Subtype.ext (Complex.conj_conj (l' : ℂ))

/- ## The invariants of the conjugate lattice -/

theorem G_conjugate (n : ℕ) : L.conjugate.G n = conj (L.G n) := by
  simp only [G]
  rw [Complex.conj_tsum, ← L.conjugateLatticeEquiv.tsum_eq]
  exact tsum_congr fun l => by
    rw [conjugateLatticeEquiv, map_inv₀, map_pow]
    ring_nf
    grind

/-- The Eisenstein sums depend only on the lattice, not on the choice of periods. -/
theorem G_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) (n : ℕ) :
    L₁.G n = L₂.G n := by
  unfold G
  rw [h]

theorem g₂_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) : L₁.g₂ = L₂.g₂ := by
  unfold g₂
  rw [G_congr h]

theorem g₃_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) : L₁.g₃ = L₂.g₃ := by
  unfold g₃
  rw [G_congr h]

theorem g₂_conjugate : L.conjugate.g₂ = conj L.g₂ := by
  simp only [g₂, G_conjugate, map_mul, map_ofNat]

theorem g₃_conjugate : L.conjugate.g₃ = conj L.g₃ := by
  simp only [g₃, G_conjugate, map_mul, map_ofNat]

/- ## Real lattices -/

/-- A period lattice is *real* if it is stable under complex conjugation. -/
def IsReal (L : PeriodPair) : Prop := L.conjugate.lattice = L.lattice

variable {L}

theorem IsReal.conj_g₂ (h : L.IsReal) : conj L.g₂ = L.g₂ := by
  rw [← L.g₂_conjugate]
  exact g₂_congr h

theorem IsReal.conj_g₃ (h : L.IsReal) : conj L.g₃ = L.g₃ := by
  rw [← L.g₃_conjugate]
  exact g₃_congr h

variable (L)

/-- A lattice is real if and only if its invariants are fixed by conjugation. The reverse
direction uses that a period lattice is determined by its invariants. -/
theorem isReal_iff : L.IsReal ↔ conj L.g₂ = L.g₂ ∧ conj L.g₃ = L.g₃ := by
  refine ⟨fun h => ⟨h.conj_g₂, h.conj_g₃⟩, fun ⟨h₂, h₃⟩ => ?_⟩
  exact lattice_eq_of_g₂_eq_of_g₃_eq (by rw [L.g₂_conjugate, h₂]) (by rw [L.g₃_conjugate, h₃])

/-- A lattice is real if and only if $g_2$ and $g_3$ are real numbers. -/
theorem isReal_iff_exists_real : L.IsReal ↔ (∃ r : ℝ, L.g₂ = r) ∧ ∃ r : ℝ, L.g₃ = r := by
  rw [L.isReal_iff, Complex.conj_eq_iff_real, Complex.conj_eq_iff_real]

end PeriodPair

end
