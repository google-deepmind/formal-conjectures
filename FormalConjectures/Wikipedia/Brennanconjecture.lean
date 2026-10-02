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
# Brennan's Conjecture

*Reference:*
- [Wikipedia](https://en.wikipedia.org/wiki/Brennan_conjecture)
- [arXiv:2409.15074](https://arxiv.org/abs/2409.15074)
- [arXiv:2512.09330](https://arxiv.org/abs/2512.09330)
-/

@[expose] public section

namespace BrennanConjecture

open Complex Filter MeasureTheory Set Topology

def unitDisk : Set ℂ := {z | ‖z‖ < 1}

/-- The standard class $\mathcal{S}$ of normalised univalent functions on $\mathbb{D}$. -/
structure IsUnivalentNormalized (f : ℂ → ℂ) : Prop where
  analyticOn : AnalyticOn ℂ f unitDisk
  injOn      : InjOn f unitDisk
  map_zero   : f 0 = 0
  deriv_zero : deriv f 0 = 1

/-- $\beta_f(\tau) := \limsup_{r \to 1^-}
\frac{\log \int_{-\pi}^{\pi} |f'(re^{i\theta})|^\tau \, d\theta}{|\log(1-r)|}$ -/
noncomputable def integralMeansSpectrum (f : ℂ → ℂ) (τ : ℝ) : ℝ :=
  limsup
    (fun r => Real.log (∫ θ in Ioc (-Real.pi) Real.pi,
        ‖deriv f (r • exp (Complex.I * θ))‖ ^ τ) /
      |Real.log (1 - r)|)
    (𝓝[Iio 1] (1 : ℝ))

noncomputable def universalSpectrum (τ : ℝ) : ℝ :=
  sSup {β | ∃ f : ℂ → ℂ, IsUnivalentNormalized f ∧ β = integralMeansSpectrum f τ}

noncomputable def universalSpectrumBounded (τ : ℝ) : ℝ :=
  sSup {β | ∃ f : ℂ → ℂ, IsUnivalentNormalized f ∧
    Bornology.IsBounded (f '' unitDisk) ∧ β = integralMeansSpectrum f τ}

@[category API, AMS 30]
theorem universalSpectrumBounded_le (τ : ℝ) :
    universalSpectrumBounded τ ≤ universalSpectrum τ := by
  apply csSup_le_csSup
  · sorry
  · sorry
  · rintro β ⟨f, hf, _, rfl⟩; exact ⟨f, hf, rfl⟩

@[category test, AMS 30]
theorem integralMeansSpectrum_id (τ : ℝ) : integralMeansSpectrum id τ = 0  := by
  have hI : (∫ θ : ℝ in Ioc (-Real.pi) Real.pi, (1:ℝ)) = 2 * Real.pi := by
    simp; rw [max_eq_left (by positivity)]; ring
  have hval : ∀ (r : ℝ) (s : ℝ), (∫ θ : ℝ in Ioc (-Real.pi) Real.pi,
        ‖deriv id (r • exp (Complex.I * θ))‖ ^ s) = 2 * Real.pi := by
    intro r _
    simp
    rw [max_eq_left (by positivity)]
    ring
  have honeA : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝 (1:ℝ)) (𝓝 (1:ℝ)) := tendsto_const_nhds
  have honeB : Tendsto id (𝓝 (1:ℝ)) (𝓝 (1:ℝ)) := tendsto_id
  have hz1 : Tendsto (fun r : ℝ => 1 - r) (𝓝 (1:ℝ)) (𝓝 (0:ℝ)) := by
    simpa using (honeA.sub honeB)
  have hzero : Tendsto (fun r : ℝ => 1 - r) (𝓝[Iio 1] (1:ℝ)) (𝓝 0) :=
    hz1.mono_left nhdsWithin_le_nhds
  have hpre : (fun r : ℝ => 1 - r) ⁻¹' (Set.Ioi 0) ∈ 𝓝[Iio 1] (1:ℝ) := by
    have h1 : Set.Iio (1:ℝ) ∈ 𝓝[Iio 1] (1:ℝ) := by
      simpa using (mem_nhdsWithin_self_inter (s := Set.Iio (1:ℝ)) (t := Set.Iio (1:ℝ))
        (x := (1:ℝ)))
    have h2 : ((fun r : ℝ => 1 - r) ⁻¹' (Set.Ioi 0)) = Set.Iio (1:ℝ) := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_Iio, Set.mem_preimage]
      constructor
      · intro h; linarith
      · intro h; linarith
    rw [h2]
    exact h1
  have hpos : Tendsto (fun r : ℝ => 1 - r) (𝓝[Iio 1] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
    refine le_inf hzero ?_
    refine (Filter.le_principal_iff.mpr ?_)
    rw [Filter.mem_map]
    exact hpre
  have hlog : Tendsto (fun r : ℝ => Real.log (1 - r)) (𝓝[Iio 1] (1:ℝ)) Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hpos
  have hneg : Tendsto (fun r : ℝ => -Real.log (1 - r)) (𝓝[Iio 1] (1:ℝ)) Filter.atTop :=
    tendsto_neg_atBot_atTop.comp hlog
  have hloginv : Tendsto (fun r : ℝ => Real.log ((1 - r)⁻¹)) (𝓝[Iio 1] (1:ℝ)) Filter.atTop :=
    hneg.congr' (by filter_upwards [] with r; rw [Real.log_inv])
  have hinv : Tendsto (fun r : ℝ => (Real.log ((1 - r)⁻¹))⁻¹) (𝓝[Iio 1] (1:ℝ)) (𝓝 0) :=
    Filter.Tendsto.inv_tendsto_atTop hloginv
  have hprod : Tendsto (fun r : ℝ => Real.log (2 * Real.pi) * (Real.log ((1 - r)⁻¹))⁻¹)
      (𝓝[Iio 1] (1:ℝ)) (𝓝 0) := by
    convert (tendsto_const_nhds.mul hinv) using 1 <;> simp
  have hpre' : ∀ᶠ r in (𝓝[Iio 1] (1:ℝ)), (0:ℝ) < 1 - r := hpre
  have hlt1 : ∀ᶠ r in (𝓝[Iio 1] (1:ℝ)), r < (1:ℝ) := by
    have h : Set.Iio (1:ℝ) ∈ 𝓝[Iio 1] (1:ℝ) := by
      simpa using (mem_nhdsWithin_self_inter (s := Set.Iio (1:ℝ)) (t := Set.Iio (1:ℝ))
        (x := (1:ℝ)))
    exact h
  have hposr : ∀ᶠ r in (𝓝[Iio 1] (1:ℝ)), (0:ℝ) < r := by
    refine mem_of_superset
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioo_mem_nhds (by norm_num : (1/2:ℝ) < 1) (by norm_num : (1:ℝ) < 3/2))) ?_
    rintro x ⟨h1, -⟩
    exact lt_trans (by norm_num : (0:ℝ) < 1/2) h1
  refine Filter.Tendsto.limsup_eq ?_
  refine hprod.congr' ?_
  filter_upwards [hpre', hlt1, hposr] with r hr1 hr2 hr3
  have habs : Real.log ((1 - r)⁻¹) = |Real.log (1 - r)| := by
    rw [Real.log_inv,
      abs_of_nonpos (a := Real.log (1 - r)) (Real.log_nonpos hr1.le (by linarith [hr3]))]
  rw [hval r τ, ← habs, div_eq_mul_inv]

/-- Brennan's conjecture, part 1: $B(-2) = 1$. -/
@[category research open, AMS 30]
theorem brennan_universalSpectrum :
    universalSpectrum (-2) = 1 := by
  sorry

/-- Brennan's conjecture, part 2: $B_b(-2) = 1$. -/
@[category research open, AMS 30]
theorem brennan_universalSpectrumBounded :
    universalSpectrumBounded (-2) = 1 := by
  sorry

/-- Brennan's conjecture, part 3: $B(-2) = B_b(-2)$. -/
@[category API, AMS 30]
theorem brennan_spectra_eq :
    universalSpectrum (-2) = universalSpectrumBounded (-2) := by
  rw [brennan_universalSpectrum, brennan_universalSpectrumBounded]

/-- Brennan's conjecture: $B(-2) = B_b(-2) = 1$. -/
@[category API, AMS 30]
theorem brennan :
    universalSpectrum (-2) = 1 ∧ universalSpectrumBounded (-2) = 1 :=
  ⟨brennan_universalSpectrum, brennan_universalSpectrumBounded⟩

end BrennanConjecture
