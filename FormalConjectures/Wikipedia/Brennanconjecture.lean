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
- [OAI26a] OpenAI, *Brennan's conjecture and sharp inverse-square integral means*.
  OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brennans-conjecture-and-sharp-inverse-square-integral-means-September-24-2026/paper.pdf
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
theorem integralMeansSpectrum_id (τ : ℝ) : integralMeansSpectrum id τ = 0 := by
  unfold integralMeansSpectrum
  have hpos : (0 : ℝ) ≤ Real.pi - -Real.pi := by
    have := Real.pi_pos
    linarith
  have habs : Filter.Tendsto (fun r : ℝ => |Real.log (1 - r)|)
      (𝓝[Iio 1] (1 : ℝ)) Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    have hb : (1 : ℝ) - Real.exp (-b) < 1 := by
      have := Real.exp_pos (-b)
      linarith
    have hIoi : Ioi (1 - Real.exp (-b)) ∈ 𝓝[Iio 1] (1 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)
    filter_upwards [hIoi, self_mem_nhdsWithin] with r hr1 hr2
    have h1 : (0 : ℝ) < 1 - r := by
      have h := mem_Iio.mp hr2
      linarith
    have h2 : 1 - r < Real.exp (-b) := by
      have h := mem_Ioi.mp hr1
      linarith
    have h3 : Real.log (1 - r) < -b := by
      have h := Real.log_lt_log h1 h2
      rwa [Real.log_exp] at h
    have h4 : b ≤ -Real.log (1 - r) := by linarith
    exact h4.trans (neg_le_abs _)
  have hmain : Filter.Tendsto (fun r : ℝ => Real.log (2 * Real.pi) / |Real.log (1 - r)|)
      (𝓝[Iio 1] (1 : ℝ)) (𝓝 0) := tendsto_const_nhds.div_atTop habs
  have heq : (fun r : ℝ => Real.log (2 * Real.pi) / |Real.log (1 - r)|) =ᶠ[𝓝[Iio 1] (1 : ℝ)]
      (fun r : ℝ => Real.log (∫ θ in Ioc (-Real.pi) Real.pi,
        ‖deriv (id : ℂ → ℂ) (r • Complex.exp (Complex.I * θ))‖ ^ τ) / |Real.log (1 - r)|) := by
    refine Filter.Eventually.of_forall fun r => ?_
    have hfun : (fun θ : ℝ => ‖deriv (id : ℂ → ℂ) (r • Complex.exp (Complex.I * θ))‖ ^ τ)
        = fun _ : ℝ => (1 : ℝ) := by
      funext θ
      simp [deriv_id]
    have hvol : volume.real (Ioc (-Real.pi) Real.pi) = 2 * Real.pi := by
      show (volume (Ioc (-Real.pi) Real.pi)).toReal = 2 * Real.pi
      rw [Real.volume_Ioc, ENNReal.toReal_ofReal hpos]
      ring
    have hint : (∫ θ in Ioc (-Real.pi) Real.pi,
        ‖deriv (id : ℂ → ℂ) (r • Complex.exp (Complex.I * θ))‖ ^ τ) = 2 * Real.pi := by
      rw [hfun, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
      exact hvol
    show Real.log (2 * Real.pi) / |Real.log (1 - r)| =
      Real.log (∫ θ in Ioc (-Real.pi) Real.pi,
        ‖deriv (id : ℂ → ℂ) (r • Complex.exp (Complex.I * θ))‖ ^ τ) / |Real.log (1 - r)|
    rw [hint]
  exact (hmain.congr' heq).limsup_eq

/-- Brennan's conjecture, part 1: $B(-2) = 1$.

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
proof. -/
@[category research solved, AMS 30, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/IntegralMeans/Main.lean#L10"]
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
