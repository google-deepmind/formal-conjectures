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
  have hsub : Tendsto (fun r : ℝ => 1 - r) (𝓝[Iio 1] (1 : ℝ)) (𝓝[Ioi 0] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (eventually_nhdsWithin_of_forall fun r hr => mem_Ioi.mpr (sub_pos.mpr hr))
    simpa using ((continuous_sub_left (1 : ℝ)).tendsto 1).mono_left nhdsWithin_le_nhds
  have habs : Tendsto (fun r : ℝ => |Real.log (1 - r)|) (𝓝[Iio 1] (1 : ℝ)) atTop :=
    tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hsub)
  simp [integralMeansSpectrum, (tendsto_const_nhds.div_atTop habs).limsup_eq]

set_option linter.style.formal_proof_palomar false in
/-- Brennan's conjecture, part 1: $B(-2) = 1$.

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
proof. The part of the linked statement used here, with its own definitions, is
`brennan_universalSpectrum.variants.uniform_bound`; see
`brennan_universalSpectrum_of_uniform_bound`. -/
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

/- ## The integral means bound of [OAI26a]

The definitions in `IntegralMeans` are copied from the Lean statement linked at
`brennan_universalSpectrum`. They differ from the ones above in four ways: univalent functions
are holomorphic (`DifferentiableOn`) rather than analytic on the disk, the integral mean carries
the factor $(2\pi)^{-1}$, the denominator is $\log(1/(1-r))$, and the spectrum is a `limsup` and
`sSup` in `EReal`. -/

namespace IntegralMeans

/-- The open unit disk, as defined in [OAI26a]. -/
def disk : Set ℂ := Metric.ball 0 1

/-- Holomorphic and injective on `U`, as defined in [OAI26a]. -/
def UnivalentOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ Set.InjOn f U

/-- Normalised univalent functions on the disk, as defined in [OAI26a]. -/
def Schlicht (f : ℂ → ℂ) : Prop :=
  UnivalentOn f disk ∧ f 0 = 0 ∧ deriv f 0 = 1

/-- The integral mean of `‖f'‖ ^ t` on the circle of radius `r`, as defined in [OAI26a]. -/
noncomputable def integralMean (f : ℂ → ℂ) (t r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi,
    ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ t

/-- The integral means spectrum of `f`, as defined in [OAI26a]. -/
noncomputable def beta (f : ℂ → ℂ) (t : ℝ) : EReal :=
  Filter.limsup (fun r : ℝ =>
    ((Real.log (integralMean f t r) / Real.log (1 / (1 - r)) : ℝ) : EReal))
    (𝓝[<] (1 : ℝ))

/-- The universal integral means spectrum, as defined in [OAI26a]. -/
noncomputable def spectrum (t : ℝ) : EReal :=
  sSup {b | ∃ f : ℂ → ℂ, Schlicht f ∧ beta f t = b}

/-- `unitDisk` is `disk`. -/
@[category API, AMS 30]
lemma unitDisk_eq_disk : unitDisk = disk := by
  ext z
  simp [unitDisk, disk]

/-- Analytic and holomorphic agree on the open disk, so the two classes of normalised univalent
functions are the same. -/
@[category API, AMS 30]
lemma isUnivalentNormalized_iff_schlicht {f : ℂ → ℂ} : IsUnivalentNormalized f ↔ Schlicht f := by
  rw [Schlicht, UnivalentOn, ← unitDisk_eq_disk]
  constructor
  · rintro ⟨ha, hi, h0, h1⟩
    exact ⟨⟨ha.differentiableOn, hi⟩, h0, h1⟩
  · rintro ⟨⟨hd, hi⟩, h0, h1⟩
    have hopen : IsOpen unitDisk := by rw [unitDisk_eq_disk]; exact Metric.isOpen_ball
    exact ⟨(hd.analyticOnNhd hopen).analyticOn, hi, h0, h1⟩

/-- The integral mean is nonnegative. -/
@[category API, AMS 30]
lemma integralMean_nonneg (f : ℂ → ℂ) (t r : ℝ) : 0 ≤ integralMean f t r :=
  mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun _ _ => by positivity)

/-- The integral in `integralMeansSpectrum` is `2π` times `integralMean`. -/
@[category API, AMS 30]
lemma integral_eq_integralMean (f : ℂ → ℂ) (t r : ℝ) :
    ∫ θ in Ioc (-Real.pi) Real.pi, ‖deriv f (r • Complex.exp (Complex.I * θ))‖ ^ t =
      2 * Real.pi * integralMean f t r := by
  rw [integralMean, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]
  simp only [Complex.real_smul, mul_comm Complex.I]

@[category API, AMS 30]
lemma tendsto_neg_log_one_sub :
    Tendsto (fun r : ℝ => -Real.log (1 - r)) (𝓝[<] (1 : ℝ)) atTop := by
  have hsub : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] (1 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (eventually_nhdsWithin_of_forall fun r hr => mem_Ioi.mpr (sub_pos.mpr hr))
    simpa using ((continuous_sub_left (1 : ℝ)).tendsto 1).mono_left nhdsWithin_le_nhds
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hsub)

/-- The ratio in `beta` is at most the ratio in `integralMeansSpectrum`: the factor
$(2\pi)^{-1}$ only lowers the logarithm. -/
@[category API, AMS 30]
lemma ratio_le_ratio (f : ℂ → ℂ) (t : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.log (integralMean f t r) / Real.log (1 / (1 - r)) ≤
      Real.log (∫ θ in Ioc (-Real.pi) Real.pi, ‖deriv f (r • Complex.exp (Complex.I * θ))‖ ^ t) /
        |Real.log (1 - r)| := by
  have hlog : Real.log (1 - r) < 0 := Real.log_neg (by linarith) (by linarith)
  rw [integral_eq_integralMean, abs_of_neg hlog, one_div, Real.log_inv,
    div_le_div_iff_of_pos_right (neg_pos.2 hlog)]
  rcases eq_or_ne (integralMean f t r) 0 with hm | hm
  · simp [hm]
  · have h2pi : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
    rw [Real.log_mul (by positivity) hm]
    linarith

/-- The uniform bound of [OAI26a] bounds the ratio in `integralMeansSpectrum` by `1 + ε` near
`1`. -/
@[category API, AMS 30]
lemma eventually_ratio_le
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ f : ℂ → ℂ, Schlicht f →
      ∀ r : ℝ, 1 / 2 ≤ r → r < 1 → integralMean f (-2) r ≤ C * (1 - r) ^ (-1 - ε))
    {f : ℂ → ℂ} (hf : IsUnivalentNormalized f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), Real.log (∫ θ in Ioc (-Real.pi) Real.pi,
      ‖deriv f (r • Complex.exp (Complex.I * θ))‖ ^ (-2 : ℝ)) / |Real.log (1 - r)| ≤ 1 + ε := by
  obtain ⟨C, hC⟩ := hbound (ε / 2) (half_pos hε)
  have hM : 0 < 2 * Real.pi * max C 1 := mul_pos (by positivity) (lt_max_of_lt_right one_pos)
  have hK : ∀ᶠ r in 𝓝[<] (1 : ℝ), Real.log (2 * Real.pi * max C 1) / -Real.log (1 - r) < ε / 2 :=
    (tendsto_order.1 (tendsto_const_nhds.div_atTop tendsto_neg_log_one_sub)).2 _ (half_pos hε)
  filter_upwards [hK, Ico_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with r hKr hr
  have hlog : Real.log (1 - r) < 0 := Real.log_neg (by linarith [hr.2]) (by linarith [hr.1])
  have hℓ : 0 < -Real.log (1 - r) := neg_pos.2 hlog
  rw [div_lt_iff₀ hℓ] at hKr
  rw [integral_eq_integralMean, abs_of_neg hlog, div_le_iff₀ hℓ]
  rcases (integralMean_nonneg f (-2) r).eq_or_lt with hm | hm
  · rw [← hm, mul_zero, Real.log_zero]
    positivity
  · have hpow : 0 < (1 - r) ^ (-1 - ε / 2) := Real.rpow_pos_of_pos (by linarith [hr.2]) _
    have h1 : integralMean f (-2) r ≤ max C 1 * (1 - r) ^ (-1 - ε / 2) :=
      (hC f (isUnivalentNormalized_iff_schlicht.1 hf) r hr.1 hr.2).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 1) hpow.le)
    have h2 : 2 * Real.pi * integralMean f (-2) r ≤
        2 * Real.pi * max C 1 * (1 - r) ^ (-1 - ε / 2) := by
      rw [mul_assoc (2 * Real.pi) (max C 1)]
      gcongr
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_mul hM.ne' hpow.ne', Real.log_rpow (by linarith [hr.2])] at h3
    linarith

/-- The uniform bound of [OAI26a] gives `integralMeansSpectrum f (-2) ≤ 1`. If the ratio is not
bounded below near `1`, then the `limsup` in `ℝ` is `0`. -/
@[category API, AMS 30]
lemma integralMeansSpectrum_le_one
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ f : ℂ → ℂ, Schlicht f →
      ∀ r : ℝ, 1 / 2 ≤ r → r < 1 → integralMean f (-2) r ≤ C * (1 - r) ^ (-1 - ε))
    {f : ℂ → ℂ} (hf : IsUnivalentNormalized f) : integralMeansSpectrum f (-2) ≤ 1 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev := eventually_ratio_le hbound hf hε
  by_cases hcob : IsCoboundedUnder (· ≤ ·) (𝓝[<] (1 : ℝ)) fun r : ℝ =>
      Real.log (∫ θ in Ioc (-Real.pi) Real.pi,
        ‖deriv f (r • Complex.exp (Complex.I * θ))‖ ^ (-2 : ℝ)) / |Real.log (1 - r)|
  · exact limsup_le_of_le hcob hev
  · rw [integralMeansSpectrum, limsup_eq]
    refine (Real.sInf_of_not_bddBelow fun hb => hcob ?_).le.trans (by linarith)
    exact hb

/-- The equality `spectrum (-2) = 1` of [OAI26a] gives, below every `b < 1`, a normalised univalent
function with `b ≤ integralMeansSpectrum f (-2)`. -/
@[category API, AMS 30]
lemma exists_le_integralMeansSpectrum
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ f : ℂ → ℂ, Schlicht f →
      ∀ r : ℝ, 1 / 2 ≤ r → r < 1 → integralMean f (-2) r ≤ C * (1 - r) ^ (-1 - ε))
    (hspec : IntegralMeans.spectrum (-2) = 1) {b : ℝ} (hb : b < 1) :
    ∃ f : ℂ → ℂ, IsUnivalentNormalized f ∧ b ≤ integralMeansSpectrum f (-2) := by
  have hlt : (b : EReal) < IntegralMeans.spectrum (-2) := by
    rw [hspec]
    exact_mod_cast hb
  obtain ⟨_, ⟨f, hf, rfl⟩, hbf⟩ := lt_sSup_iff.1 hlt
  have hf' := isUnivalentNormalized_iff_schlicht.2 hf
  refine ⟨f, hf', le_limsup_of_frequently_le ?_
    (isBoundedUnder_of_eventually_le (eventually_ratio_le hbound hf' one_pos))⟩
  exact ((frequently_lt_of_lt_limsup (by isBoundedDefault) hbf).and_eventually
    (Ioo_mem_nhdsLT one_pos)).mono fun r ⟨h1, h2⟩ =>
      (EReal.coe_lt_coe_iff.1 h1).le.trans (ratio_le_ratio f (-2) h2.1 h2.2)

end IntegralMeans

set_option linter.style.formal_proof_palomar false in
/-- For every $\varepsilon > 0$ there is $C_\varepsilon$ such that every normalised univalent
function satisfies
$$\frac{1}{2\pi} \int_{-\pi}^{\pi} |f'(re^{i\theta})|^{-2} \, d\theta
  \le C_\varepsilon (1 - r)^{-1-\varepsilon}$$
for $1/2 \le r < 1$, and the universal spectrum at $-2$ is $1$, with the definitions in
`IntegralMeans`.

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean proof.
The linked statement also gives the integrability of $|\varphi'|^s$ for $4/3 < s < 4$ for conformal
maps onto the disk and of $|f'|^t$ for $-2 < t < 2/3$. -/
@[category research solved, AMS 30, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/IntegralMeans/Main.lean#L10"]
theorem brennan_universalSpectrum.variants.uniform_bound :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ f : ℂ → ℂ, IntegralMeans.Schlicht f →
      ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
        IntegralMeans.integralMean f (-2) r ≤ C * (1 - r) ^ (-1 - ε)) ∧
    IntegralMeans.spectrum (-2) = 1 := by
  sorry

/-- The statement of [OAI26a] implies `brennan_universalSpectrum`: the uniform bound gives
`integralMeansSpectrum f (-2) ≤ 1` for every `f`, and `spectrum (-2) = 1` gives functions with
spectrum arbitrarily close to `1`. -/
@[category test, AMS 30]
theorem brennan_universalSpectrum_of_uniform_bound
    (h : type_of% @brennan_universalSpectrum.variants.uniform_bound) :
    type_of% @brennan_universalSpectrum := by
  obtain ⟨hbound, hspec⟩ := h
  have hle : ∀ β ∈ {β | ∃ f : ℂ → ℂ, IsUnivalentNormalized f ∧ β = integralMeansSpectrum f (-2)},
      β ≤ 1 := by
    rintro β ⟨f, hf, rfl⟩
    exact IntegralMeans.integralMeansSpectrum_le_one hbound hf
  refine le_antisymm (Real.sSup_le hle zero_le_one) (le_of_forall_lt_imp_le_of_dense fun b hb => ?_)
  obtain ⟨f, hf, hbf⟩ := IntegralMeans.exists_le_integralMeansSpectrum hbound hspec hb
  exact hbf.trans (le_csSup ⟨1, hle⟩ ⟨f, hf, rfl⟩)

end BrennanConjecture
