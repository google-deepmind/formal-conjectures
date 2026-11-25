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
proof. -/
@[category research solved, AMS 30, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/IntegralMeans/Main.lean#L10"]
theorem brennan_universalSpectrum :
    universalSpectrum (-2) = 1 := by
  sorry

/-- Brennan's conjecture, part 2: $B_b(-2) = 1$.

This follows immediately from the uniform bound $\beta_f(-2) \le 1$ for all $f \in \mathcal{S}$
proved in [OAI26a] (which gives $B_b(-2) \le B(-2) = 1$), together with the elementary bounded
normalised univalent witness $f(z) = z - z^2 / 2$, whose derivative $f'(z) = 1 - z$ yields
$\beta_f(-2) \ge 1$ (see `brennan_universalSpectrumBounded_of_le_one`). -/
@[category research solved, AMS 30]
theorem brennan_universalSpectrumBounded :
    universalSpectrumBounded (-2) = 1 := by
  sorry

/-- The bounded universal spectrum at $\tau = -2$ equals $1$ once every normalised univalent
function satisfies $\beta_f(-2) \le 1$ (as proved in [OAI26a]): the lower bound is achieved by
the elementary bounded normalised univalent polynomial $f(z) = z - z^2 / 2$. -/
@[category API, AMS 30]
theorem brennan_universalSpectrumBounded_of_le_one
    (h : ∀ f : ℂ → ℂ, IsUnivalentNormalized f → integralMeansSpectrum f (-2) ≤ 1) :
    universalSpectrumBounded (-2) = 1 := by
  let f : ℂ → ℂ := fun z => z - z ^ 2 / 2
  have hderiv : ∀ z : ℂ, deriv f z = 1 - z := fun z => by
    have hd : HasDerivAt f (1 - z) z := by
      have h1 : HasDerivAt f (1 - ((2 : ℕ) : ℂ) * z ^ (2 - 1) / 2) z :=
        (hasDerivAt_id z).sub ((hasDerivAt_pow 2 z).div_const (2 : ℂ))
      rwa [show (1 : ℂ) - ((2 : ℕ) : ℂ) * z ^ (2 - 1) / 2 = 1 - z by norm_num] at h1
    exact hd.deriv
  have hf : IsUnivalentNormalized f :=
    { analyticOn :=
        (analyticOnNhd_id.sub
          ((analyticOnNhd_id.pow 2).div analyticOnNhd_const fun _ _ => two_ne_zero)).analyticOn
      injOn := fun z hz w hw hzw => by
        have hfac : (z - w) * (2 - (z + w)) = 0 := by linear_combination 2 * hzw
        rcases mul_eq_zero.mp hfac with h0 | h2
        · exact sub_eq_zero.mp h0
        · exfalso
          have hnorm : ‖z + w‖ < 2 := by
            calc ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le z w
              _ < 1 + 1 := add_lt_add hz hw
              _ = 2 := by norm_num
          have h2eq : z + w = 2 := (sub_eq_zero.mp h2).symm
          rw [h2eq] at hnorm; norm_num at hnorm
      map_zero := by simp [f]
      deriv_zero := by simp [hderiv] }
  have hbdd : Bornology.IsBounded (f '' unitDisk) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨2, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hz' : ‖z‖ < 1 := hz
    calc ‖z - z ^ 2 / 2‖ ≤ ‖z‖ + ‖z ^ 2 / 2‖ := norm_sub_le _ _
      _ = ‖z‖ + ‖z‖ ^ 2 / 2 := by simp [norm_pow]
      _ ≤ 2 := by nlinarith [norm_nonneg z]
  have hsub : Tendsto (fun r : ℝ => 1 - r) (𝓝[Iio 1] (1 : ℝ)) (𝓝[Ioi 0] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (eventually_nhdsWithin_of_forall fun r hr => mem_Ioi.mpr (sub_pos.mpr hr))
    simpa using ((continuous_sub_left (1 : ℝ)).tendsto 1).mono_left nhdsWithin_le_nhds
  have habs : Tendsto (fun r : ℝ => |Real.log (1 - r)|) (𝓝[Iio 1] (1 : ℝ)) atTop :=
    tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hsub)
  have hev : ∀ᶠ r : ℝ in 𝓝[Iio 1] (1 : ℝ), 1 / 2 < r ∧ r < 1 :=
    (eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))).and self_mem_nhdsWithin
  have hratio : ∀ᶠ r : ℝ in 𝓝[Iio 1] (1 : ℝ),
      1 - Real.log 2 / |Real.log (1 - r)| ≤
        Real.log (∫ θ in Ioc (-Real.pi) Real.pi,
          ‖deriv f (r • exp (Complex.I * θ))‖ ^ (-2 : ℝ)) / |Real.log (1 - r)| ∧
      Real.log (∫ θ in Ioc (-Real.pi) Real.pi,
          ‖deriv f (r • exp (Complex.I * θ))‖ ^ (-2 : ℝ)) / |Real.log (1 - r)| ≤
        2 + Real.log (2 * Real.pi) / |Real.log (1 - r)| := by
    filter_upwards [hev] with r ⟨hr12, hr1⟩
    set δ : ℝ := 1 - r
    have hδpos : 0 < δ := by linarith
    have hδlt : δ < 1 / 2 := by linarith
    have hrpos : 0 < r := by linarith
    have hδpi : δ < Real.pi := hδlt.trans (by linarith [Real.pi_gt_three])
    have hlogneg : Real.log δ < 0 := Real.log_neg hδpos (by linarith)
    have habslog : |Real.log δ| = -Real.log δ := abs_of_neg hlogneg
    have habspos : 0 < |Real.log δ| := by linarith
    have hnorm_lo : ∀ θ : ℝ, δ ≤ ‖1 - r • exp (Complex.I * θ)‖ := fun θ => by
      have hexp : ‖r • exp (Complex.I * θ)‖ = r := by
        rw [norm_smul, Real.norm_of_nonneg hrpos.le, mul_comm Complex.I,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      have := norm_sub_norm_le (1 : ℂ) (r • exp (Complex.I * θ))
      simp only [norm_one, hexp] at this
      linarith
    have hcont :
        Continuous (fun θ : ℝ => ‖1 - r • exp (Complex.I * θ)‖ ^ (-2 : ℝ)) := by
      refine Continuous.rpow_const ?_ (fun θ => Or.inl (by linarith [hnorm_lo θ]))
      fun_prop
    have hint_pi : IntegrableOn (fun θ : ℝ => ‖1 - r • exp (Complex.I * θ)‖ ^ (-2 : ℝ))
        (Ioc (-Real.pi) Real.pi) := hcont.integrableOn_Ioc
    have hI_lo : (2 * δ)⁻¹ ≤ ∫ θ in Ioc (-Real.pi) Real.pi,
        ‖1 - r • exp (Complex.I * θ)‖ ^ (-2 : ℝ) := by
      have hsub_ioc : Ioc (-δ) δ ⊆ Ioc (-Real.pi) Real.pi :=
        Ioc_subset_Ioc (by linarith) (by linarith)
      have hpt : ∀ θ ∈ Ioc (-δ) δ,
          (2 * δ) ^ (-2 : ℝ) ≤ ‖1 - r • exp (Complex.I * θ)‖ ^ (-2 : ℝ) := by
        intro θ hθ
        have hθabs : |θ| ≤ δ := abs_le.mpr ⟨hθ.1.le, hθ.2⟩
        have hexp_sub : ‖exp (Complex.I * θ) - 1‖ ≤ |θ| := by
          have h1 :
              ‖exp (Complex.I * θ) - exp (Complex.I * (0 : ℝ))‖ ≤ (1 : ℝ) * ‖θ - 0‖ := by
            refine Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
              (f := fun t : ℝ => exp (Complex.I * t)) ?_ ?_ convex_univ (mem_univ 0) (mem_univ θ)
            · intro t _
              have hd : HasDerivAt (fun s : ℝ => exp (Complex.I * (s : ℂ)))
                  (exp (Complex.I * (t : ℂ)) * Complex.I) t := by
                have := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I
                simpa [mul_comm] using this.cexp
              exact hd.differentiableAt
            · intro t _
              have hd : HasDerivAt (fun s : ℝ => exp (Complex.I * (s : ℂ)))
                  (exp (Complex.I * (t : ℂ)) * Complex.I) t := by
                have := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I
                simpa [mul_comm] using this.cexp
              rw [hd.deriv, norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I,
                Complex.norm_I, mul_one]
          simpa using h1
        have hup : ‖1 - r • exp (Complex.I * θ)‖ ≤ 2 * δ := by
          have heq : (1 : ℂ) - r • exp (Complex.I * θ) =
              ((δ : ℂ) - (r : ℂ) * (exp (Complex.I * θ) - 1)) := by
            simp only [δ, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]; ring
          rw [heq]
          calc ‖(δ : ℂ) - (r : ℂ) * (exp (Complex.I * θ) - 1)‖
              ≤ ‖(δ : ℂ)‖ + ‖(r : ℂ) * (exp (Complex.I * θ) - 1)‖ := norm_sub_le _ _
            _ = δ + r * ‖exp (Complex.I * θ) - 1‖ := by
                rw [Complex.norm_real, Real.norm_of_nonneg hδpos.le, norm_mul,
                  Complex.norm_real, Real.norm_of_nonneg hrpos.le]
            _ ≤ δ + 1 * δ := by nlinarith [norm_nonneg (exp (Complex.I * θ) - 1)]
            _ = 2 * δ := by ring
        exact Real.rpow_le_rpow_of_nonpos (by linarith [hnorm_lo θ]) hup (by norm_num)
      calc (2 * δ)⁻¹ = (2 * δ) * (2 * δ) ^ (-2 : ℝ) := by
              rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
                Real.rpow_natCast]
              field_simp
        _ = ∫ _ in Ioc (-δ) δ, (2 * δ) ^ (-2 : ℝ) := by
              rw [MeasureTheory.setIntegral_const, smul_eq_mul,
                Real.volume_real_Ioc_of_le (by linarith : -δ ≤ δ)]
              ring
        _ ≤ ∫ θ in Ioc (-δ) δ, ‖1 - r • exp (Complex.I * θ)‖ ^ (-2 : ℝ) :=
              setIntegral_mono_on (integrableOn_const (by simp))
                (hint_pi.mono_set hsub_ioc) measurableSet_Ioc hpt
        _ ≤ ∫ θ in Ioc (-Real.pi) Real.pi, ‖1 - r • exp (Complex.I * θ)‖ ^ (-2 : ℝ) :=
              setIntegral_mono_set hint_pi
                (Eventually.of_forall fun θ => Real.rpow_nonneg (norm_nonneg _) _)
                (Eventually.of_forall fun θ hθ => hsub_ioc hθ)
    have hI_hi :
        ∫ θ in Ioc (-Real.pi) Real.pi, ‖1 - r • exp (Complex.I * θ)‖ ^ (-2 : ℝ) ≤
          2 * Real.pi * δ ^ (-2 : ℝ) := by
      calc ∫ θ in Ioc (-Real.pi) Real.pi, ‖1 - r • exp (Complex.I * θ)‖ ^ (-2 : ℝ)
          ≤ ∫ _ in Ioc (-Real.pi) Real.pi, δ ^ (-2 : ℝ) :=
            setIntegral_mono_on hint_pi (integrableOn_const (by simp)) measurableSet_Ioc
              (fun θ _ => Real.rpow_le_rpow_of_nonpos hδpos (hnorm_lo θ) (by norm_num))
        _ = 2 * Real.pi * δ ^ (-2 : ℝ) := by
            rw [MeasureTheory.setIntegral_const, smul_eq_mul,
              Real.volume_real_Ioc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
            ring
    have hI_pos :
        0 < ∫ θ in Ioc (-Real.pi) Real.pi, ‖1 - r • exp (Complex.I * θ)‖ ^ (-2 : ℝ) :=
      lt_of_lt_of_le (by positivity) hI_lo
    simp_rw [hderiv]
    constructor
    · rw [le_div_iff₀ habspos]
      have hlog := Real.log_le_log (by positivity) hI_lo
      rw [Real.log_inv, Real.log_mul (by norm_num) hδpos.ne'] at hlog
      have : (1 - Real.log 2 / |Real.log δ|) * |Real.log δ| = -(Real.log 2 + Real.log δ) := by
        rw [sub_mul, one_mul, div_mul_cancel₀ _ habspos.ne', habslog]; ring
      linarith
    · rw [div_le_iff₀ habspos]
      have hlog := Real.log_le_log hI_pos hI_hi
      rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hδpos _).ne',
        Real.log_rpow hδpos] at hlog
      have : (2 + Real.log (2 * Real.pi) / |Real.log δ|) * |Real.log δ| =
          Real.log (2 * Real.pi) + (-2) * Real.log δ := by
        rw [add_mul, div_mul_cancel₀ _ habspos.ne', habslog]; ring
      linarith
  have hlo_lim : Tendsto (fun r : ℝ => 1 - Real.log 2 / |Real.log (1 - r)|)
      (𝓝[Iio 1] (1 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop habs)
  have hhi_lim : Tendsto (fun r : ℝ => 2 + Real.log (2 * Real.pi) / |Real.log (1 - r)|)
      (𝓝[Iio 1] (1 : ℝ)) (𝓝 2) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop habs)
  have hspec : 1 ≤ integralMeansSpectrum f (-2) := by
    rw [← hlo_lim.limsup_eq]
    refine limsup_le_limsup (hratio.mono fun r hr => hr.1) ?_ ?_
    · exact hlo_lim.isCoboundedUnder_le
    · refine isBoundedUnder_of_eventually_le (a := 3) ?_
      filter_upwards [hratio, hhi_lim.eventually (eventually_lt_nhds (by norm_num : (2 : ℝ) < 3))]
        with r hr hlt
      exact hr.2.trans hlt.le
  refine le_antisymm ?_ ?_
  · exact csSup_le ⟨integralMeansSpectrum f (-2), f, hf, hbdd, rfl⟩
      (by rintro _ ⟨g, hg, -, rfl⟩; exact h g hg)
  · exact hspec.trans (le_csSup ⟨1, by rintro _ ⟨g, hg, -, rfl⟩; exact h g hg⟩
      ⟨f, hf, hbdd, rfl⟩)

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
