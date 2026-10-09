import WeilPairedHadamardKernelTsumV2
import Mathlib.Tactic

/-!
AEGIS Ω — fixed-line paired-zero Fubini majorant core v3.

This module kernelizes the absolute product-integral estimate (FZ) from the
#490 paired-Hadamard proof note.  It is deliberately stated for an abstract
vertical profile H carrying the three weighted L1 moments actually used by
the proof.  A subsequent module will bind those moments to the concrete
compact-smooth Mellin profile via Mathlib Schwartz integrability.

No contour shift, normalized explicit-formula assembly, arithmetic sign
inequality, global Weil positivity, or RH implication is asserted here.
-/

open Complex MeasureTheory Filter
open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-- Paired nontrivial-zero kernel on the fixed line Re(s)=c. -/
def WeilPairedZeroKernelV3
    (c t : ℝ) (ρ : LiCriterion.NontrivialZero) : ℂ :=
  1 / (((c : ℂ) + (t : ℂ) * I) - ρ.val) +
  1 / (((c : ℂ) + (t : ℂ) * I) - (1 - ρ.val))

/-- Exactly the L1 moments needed by the FZ split: H itself, |t|H, and
|t|^2 H.  The first field also supplies strong measurability of H. -/
def HasVerticalNormMomentsTwoV3 (H : ℝ → ℂ) : Prop :=
  Integrable H ∧
  Integrable (fun t : ℝ => |t| * ‖H t‖) ∧
  Integrable (fun t : ℝ => |t| ^ 2 * ‖H t‖)

private theorem weil_fixed_line_denom_left_ne_v3
    (c t : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c) :
    ((c : ℂ) + (t : ℂ) * I) - ρ.val ≠ 0 := by
  intro h
  have heq : ((c : ℂ) + (t : ℂ) * I) = ρ.val := sub_eq_zero.mp h
  have hre := congrArg Complex.re heq
  simp at hre
  linarith [ρ.property.2.2]

private theorem weil_fixed_line_denom_right_ne_v3
    (c t : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c) :
    ((c : ℂ) + (t : ℂ) * I) - (1 - ρ.val) ≠ 0 := by
  intro h
  have heq : ((c : ℂ) + (t : ℂ) * I) = 1 - ρ.val := sub_eq_zero.mp h
  have hre := congrArg Complex.re heq
  simp at hre
  linarith [ρ.property.2.1]

/-- Exact paired rational identity, restricted to the actual fixed-line regime
c>1 so Lean's totalized division never encounters a pole. -/
theorem weil_paired_zero_kernel_eq_quotient_v3
    (c t : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c) :
    WeilPairedZeroKernelV3 c t ρ =
      (2 * ((c : ℂ) + (t : ℂ) * I) - 1) /
        ((((c : ℂ) + (t : ℂ) * I) - ρ.val) *
          (((c : ℂ) + (t : ℂ) * I) - (1 - ρ.val))) := by
  unfold WeilPairedZeroKernelV3
  have h₁ := weil_fixed_line_denom_left_ne_v3 c t ρ hc
  have h₂ := weil_fixed_line_denom_right_ne_v3 c t ρ hc
  field_simp [h₁, h₂]
  ring

private theorem weil_paired_zero_kernel_continuous_v3
    (c : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c) :
    Continuous (fun t : ℝ => WeilPairedZeroKernelV3 c t ρ) := by
  unfold WeilPairedZeroKernelV3
  have h₁ : Continuous
      (fun t : ℝ => ((c : ℂ) + (t : ℂ) * I) - ρ.val) := by
    fun_prop
  have h₂ : Continuous
      (fun t : ℝ => ((c : ℂ) + (t : ℂ) * I) - (1 - ρ.val)) := by
    fun_prop
  exact
    (continuous_const.div h₁ (fun t => weil_fixed_line_denom_left_ne_v3 c t ρ hc)).add
      (continuous_const.div h₂ (fun t => weil_fixed_line_denom_right_ne_v3 c t ρ hc))

private theorem weil_paired_zero_kernel_global_norm_bound_v3
    (c t : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c) :
    ‖WeilPairedZeroKernelV3 c t ρ‖ ≤ 2 / (c - 1) := by
  let δ : ℝ := c - 1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let d₁ : ℂ := ((c : ℂ) + (t : ℂ) * I) - ρ.val
  let d₂ : ℂ := ((c : ℂ) + (t : ℂ) * I) - (1 - ρ.val)
  have hd₁ : δ ≤ ‖d₁‖ := by
    have hre : δ ≤ d₁.re := by
      dsimp [δ, d₁]
      simp
      linarith [ρ.property.2.2]
    exact hre.trans (Complex.re_le_norm d₁)
  have hd₂ : δ ≤ ‖d₂‖ := by
    have hre : δ ≤ d₂.re := by
      dsimp [δ, d₂]
      simp
      linarith [ρ.property.2.1]
    exact hre.trans (Complex.re_le_norm d₂)
  have hi₁ : ‖(1 : ℂ) / d₁‖ ≤ 1 / δ := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hδ hd₁
  have hi₂ : ‖(1 : ℂ) / d₂‖ ≤ 1 / δ := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hδ hd₂
  change ‖(1 : ℂ) / d₁ + (1 : ℂ) / d₂‖ ≤ 2 / δ
  calc
    ‖(1 : ℂ) / d₁ + (1 : ℂ) / d₂‖
        ≤ ‖(1 : ℂ) / d₁‖ + ‖(1 : ℂ) / d₂‖ := norm_add_le _ _
    _ ≤ 1 / δ + 1 / δ := add_le_add hi₁ hi₂
    _ = 2 / δ := by ring

private theorem weil_paired_zero_kernel_central_norm_bound_v3
    (c t : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c)
    (hh : 1 ≤ |ρ.val.im|) (ht : |t| ≤ |ρ.val.im| / 2) :
    ‖WeilPairedZeroKernelV3 c t ρ‖ ≤
      4 * (2 * c + 1 + 2 * |t|) / |ρ.val.im| ^ 2 := by
  let h : ℝ := |ρ.val.im|
  have hpos : 0 < h := lt_of_lt_of_le zero_lt_one (by simpa [h] using hh)
  let z : ℂ := (c : ℂ) + (t : ℂ) * I
  let d₁ : ℂ := z - ρ.val
  let d₂ : ℂ := z - (1 - ρ.val)
  have him₁ : h / 2 ≤ |t - ρ.val.im| := by
    have htri : h ≤ |t - ρ.val.im| + |t| := by
      calc
        h = |(t - ρ.val.im) + (-t)| := by
          dsimp [h]
          rw [show (t - ρ.val.im) + (-t) = -ρ.val.im by ring, abs_neg]
        _ ≤ |t - ρ.val.im| + |-t| := abs_add_le _ _
        _ = |t - ρ.val.im| + |t| := by rw [abs_neg]
    linarith
  have him₂ : h / 2 ≤ |t + ρ.val.im| := by
    have htri : h ≤ |t + ρ.val.im| + |t| := by
      calc
        h = |(t + ρ.val.im) + (-t)| := by
          dsimp [h]
          rw [show (t + ρ.val.im) + (-t) = ρ.val.im by ring]
        _ ≤ |t + ρ.val.im| + |-t| := abs_add_le _ _
        _ = |t + ρ.val.im| + |t| := by rw [abs_neg]
    linarith
  have hd₁ : h / 2 ≤ ‖d₁‖ := by
    have hi := Complex.abs_im_le_norm d₁
    have hi' : |t - ρ.val.im| ≤ ‖d₁‖ := by
      simpa [d₁, z] using hi
    exact him₁.trans hi'
  have hd₂ : h / 2 ≤ ‖d₂‖ := by
    have hi := Complex.abs_im_le_norm d₂
    have hi' : |t + ρ.val.im| ≤ ‖d₂‖ := by
      simpa [d₂, z] using hi
    exact him₂.trans hi'
  have hprod : (h / 2) ^ 2 ≤ ‖d₁‖ * ‖d₂‖ := by
    have hm := mul_le_mul hd₁ hd₂ (by positivity) (norm_nonneg d₁)
    nlinarith
  have hnum : ‖2 * z - 1‖ ≤ 2 * c + 1 + 2 * |t| := by
    have hn := Complex.norm_le_abs_re_add_abs_im (2 * z - 1)
    have hcpos : 0 < 2 * c - 1 := by linarith
    calc
      ‖2 * z - 1‖ ≤ |(2 * z - 1).re| + |(2 * z - 1).im| := hn
      _ = |2 * c - 1| + |2 * t| := by simp [z]
      _ = (2 * c - 1) + 2 * |t| := by
        rw [abs_of_pos hcpos]
        simp [abs_mul]
      _ ≤ 2 * c + 1 + 2 * |t| := by linarith
  have hinv :
      (1 : ℝ) / (‖d₁‖ * ‖d₂‖) ≤ 4 / h ^ 2 := by
    have hhalf : 0 < (h / 2) ^ 2 := by positivity
    have h0 := one_div_le_one_div_of_le hhalf hprod
    have heq : (1 : ℝ) / (h / 2) ^ 2 = 4 / h ^ 2 := by
      field_simp [ne_of_gt hpos]
      ring
    exact h0.trans_eq heq
  rw [weil_paired_zero_kernel_eq_quotient_v3 c t ρ hc, norm_div, norm_mul]
  have hm := mul_le_mul hnum hinv (by positivity) (by positivity)
  simpa [z, d₁, d₂, h, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hm

private theorem riemannXi_paired_kernel_product_integral_eventually_bound_v3
    (H : ℝ → ℂ) (c : ℝ) (hc : 1 < c)
    (hH : HasVerticalNormMomentsTwoV3 H) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ ρ : LiCriterion.NontrivialZero in cofinite,
        (∫ t : ℝ, ‖WeilPairedZeroKernelV3 c t ρ * H t‖) ≤
          2 * M / ‖ρ.val‖ ^ 2 := by
  classical
  let δ : ℝ := c - 1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let C : ℝ → ℝ := fun t =>
    4 * (2 * c + 1) * ‖H t‖ +
    8 * (|t| * ‖H t‖) +
    (8 / δ) * (|t| ^ 2 * ‖H t‖)
  have hCint : Integrable C := by
    have hsum :=
      ((hH.1.norm.const_mul (4 * (2 * c + 1))).fun_add
        (hH.2.1.const_mul 8)).fun_add
        (hH.2.2.const_mul (8 / δ))
    simpa only [C] using hsum
  have hCnonneg : ∀ t : ℝ, 0 ≤ C t := by
    intro t
    dsimp [C]
    positivity
  let M : ℝ := ∫ t : ℝ, C t
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg hCnonneg
  refine ⟨M, hM, ?_⟩

  have hgenus :=
    LiCriterion.xi_genus_one_of_hadamard_order_one
      LiCriterion.XiGrowth.riemannXi_hasFiniteOrder
      LiCriterion.XiGrowth.riemannXi_order_le_one
  have hsmall :
      ∀ᶠ ρ : LiCriterion.NontrivialZero in cofinite,
        (1 : ℝ) / ‖ρ.val‖ ^ 2 < (1 / 4 : ℝ) :=
    hgenus.tendsto_cofinite_zero.eventually_lt_const (by norm_num)

  filter_upwards [hsmall] with ρ hρsmall
  have hρnormpos : 0 < ‖ρ.val‖ := norm_pos_iff.mpr ρ.ne_zero
  have hρnorm : 2 < ‖ρ.val‖ := by
    by_contra hnot
    have hle : ‖ρ.val‖ ≤ 2 := le_of_not_gt hnot
    have hinv :
        (1 / 4 : ℝ) ≤ (1 : ℝ) / ‖ρ.val‖ ^ 2 := by
      rw [div_le_div_iff₀ (by norm_num) (sq_pos_of_pos hρnormpos)]
      nlinarith
    exact (not_le_of_gt hρsmall) hinv

  let h : ℝ := |ρ.val.im|
  have hreabs : |ρ.val.re| = ρ.val.re := abs_of_pos ρ.property.2.1
  have hnorm_le : ‖ρ.val‖ ≤ ρ.val.re + h := by
    have hn := Complex.norm_le_abs_re_add_abs_im ρ.val
    simpa [h, hreabs] using hn
  have hh : 1 < h := by
    by_contra hnot
    have hhle : h ≤ 1 := le_of_not_gt hnot
    have : ‖ρ.val‖ < 2 := by
      exact hnorm_le.trans_lt (by linarith [ρ.property.2.2])
    linarith
  have hh1 : 1 ≤ h := le_of_lt hh
  have hpos : 0 < h := zero_lt_one.trans hh

  have hkernel_meas :
      AEStronglyMeasurable
        (fun t : ℝ => WeilPairedZeroKernelV3 c t ρ * H t) := by
    exact
      (weil_paired_zero_kernel_continuous_v3 c ρ hc).aestronglyMeasurable.mul
        hH.1.aestronglyMeasurable

  have hpoint : ∀ t : ℝ,
      ‖WeilPairedZeroKernelV3 c t ρ * H t‖ ≤ C t / h ^ 2 := by
    intro t
    by_cases ht : |t| ≤ h / 2
    · have hk :=
        weil_paired_zero_kernel_central_norm_bound_v3
          c t ρ hc (by simpa [h] using hh1) (by simpa [h] using ht)
      have hmain :
          4 * (2 * c + 1 + 2 * |t|) * ‖H t‖ ≤ C t := by
        have hextra : 0 ≤ (8 / δ) * |t| ^ 2 * ‖H t‖ := by positivity
        dsimp [C]
        nlinarith
      calc
        ‖WeilPairedZeroKernelV3 c t ρ * H t‖
            = ‖WeilPairedZeroKernelV3 c t ρ‖ * ‖H t‖ := norm_mul _ _
        _ ≤ (4 * (2 * c + 1 + 2 * |t|) / h ^ 2) * ‖H t‖ :=
          mul_le_mul_of_nonneg_right (by simpa [h] using hk) (norm_nonneg _)
        _ = (4 * (2 * c + 1 + 2 * |t|) * ‖H t‖) / h ^ 2 := by ring
        _ ≤ C t / h ^ 2 := by
          simp only [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hmain (inv_nonneg.mpr (sq_nonneg h))
    · have ht' : h / 2 < |t| := lt_of_not_ge ht
      have hsq : h ^ 2 ≤ 4 * |t| ^ 2 := by
        have h₁ : 0 ≤ 2 * |t| - h := by linarith [abs_nonneg t]
        have h₂ : 0 ≤ 2 * |t| + h := by positivity
        have hm : 0 ≤ (2 * |t| - h) * (2 * |t| + h) :=
          mul_nonneg h₁ h₂
        nlinarith
      have hk := weil_paired_zero_kernel_global_norm_bound_v3 c t ρ hc
      have hcoef : 0 ≤ (2 / δ) * ‖H t‖ := by positivity
      have htail :
          (2 / δ) * ‖H t‖ ≤
            ((8 / δ) * |t| ^ 2 * ‖H t‖) / h ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hpos)).2
        have hm := mul_le_mul_of_nonneg_left hsq hcoef
        calc
          (2 / δ) * ‖H t‖ * h ^ 2
              ≤ (2 / δ) * ‖H t‖ * (4 * |t| ^ 2) := hm
          _ = (8 / δ) * |t| ^ 2 * ‖H t‖ := by ring
      have htailC : (8 / δ) * |t| ^ 2 * ‖H t‖ ≤ C t := by
        have h₀ : 0 ≤ 4 * (2 * c + 1) * ‖H t‖ := by positivity
        have h₁ : 0 ≤ 8 * |t| * ‖H t‖ := by positivity
        dsimp [C]
        nlinarith
      calc
        ‖WeilPairedZeroKernelV3 c t ρ * H t‖
            = ‖WeilPairedZeroKernelV3 c t ρ‖ * ‖H t‖ := norm_mul _ _
        _ ≤ (2 / δ) * ‖H t‖ :=
          mul_le_mul_of_nonneg_right (by simpa [δ] using hk) (norm_nonneg _)
        _ ≤ ((8 / δ) * |t| ^ 2 * ‖H t‖) / h ^ 2 := htail
        _ ≤ C t / h ^ 2 := by
          simp only [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right htailC (inv_nonneg.mpr (sq_nonneg h))

  have hdomint : Integrable (fun t : ℝ => C t / h ^ 2) := by
    simpa [div_eq_mul_inv, mul_comm] using
      hCint.mul_const ((h ^ 2)⁻¹)
  have hprodint :
      Integrable (fun t : ℝ => WeilPairedZeroKernelV3 c t ρ * H t) :=
    hdomint.mono' hkernel_meas (ae_of_all _ hpoint)
  have hint :
      (∫ t : ℝ, ‖WeilPairedZeroKernelV3 c t ρ * H t‖) ≤
        M / h ^ 2 := by
    calc
      (∫ t : ℝ, ‖WeilPairedZeroKernelV3 c t ρ * H t‖)
          ≤ ∫ t : ℝ, C t / h ^ 2 :=
        integral_mono hprodint.norm hdomint hpoint
      _ = M / h ^ 2 := by
        dsimp [M]
        simp only [div_eq_mul_inv]
        rw [integral_mul_const]

  have hre2 : ρ.val.re ^ 2 ≤ 1 := by
    nlinarith [ρ.property.2.1, ρ.property.2.2]
  have hh2 : 1 ≤ h ^ 2 := by nlinarith
  have hnormsq : ‖ρ.val‖ ^ 2 ≤ 2 * h ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [h]
    nlinarith [sq_abs ρ.val.im]
  have hinvrel :
      (1 : ℝ) / h ^ 2 ≤ 2 / ‖ρ.val‖ ^ 2 := by
    exact
      (div_le_div_iff₀ (sq_pos_of_pos hpos) (sq_pos_of_pos hρnormpos)).2
        (by simpa using hnormsq)
  have hscaled : M / h ^ 2 ≤ 2 * M / ‖ρ.val‖ ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hinvrel hM
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hm
  exact hint.trans hscaled

/-- FZ core: the multiplicity-weighted product-integral family is summable.
This is the exact absolute-convergence certificate needed before exchanging
the zero sum with the fixed-line integral. -/
theorem riemannXi_paired_kernel_product_integral_summable_v3
    (H : ℝ → ℂ) (c : ℝ) (hc : 1 < c)
    (hH : HasVerticalNormMomentsTwoV3 H) :
    Summable (fun ρ : LiCriterion.NontrivialZero =>
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℝ) *
        ∫ t : ℝ, ‖WeilPairedZeroKernelV3 c t ρ * H t‖) := by
  classical
  obtain ⟨M, hM, hbound⟩ :=
    riemannXi_paired_kernel_product_integral_eventually_bound_v3 H c hc hH
  have hweighted :=
    LiCriterion.xi_weighted_genus_one_of_hadamard_order_one
      LiCriterion.XiGrowth.riemannXi_hasFiniteOrder
      LiCriterion.XiGrowth.riemannXi_order_le_one
  have hdom :
      Summable (fun ρ : LiCriterion.NontrivialZero =>
        (2 * M) *
          ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℝ) /
            ‖ρ.val‖ ^ 2)) :=
    hweighted.mul_left (2 * M)
  refine Summable.of_norm_bounded_eventually hdom ?_
  filter_upwards [hbound] with ρ hρ
  have hint_nonneg :
      0 ≤ ∫ t : ℝ, ‖WeilPairedZeroKernelV3 c t ρ * H t‖ :=
    integral_nonneg (fun t => norm_nonneg _)
  have hmul_nonneg :
      0 ≤ (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℝ) *
        ∫ t : ℝ, ‖WeilPairedZeroKernelV3 c t ρ * H t‖ :=
    mul_nonneg (Nat.cast_nonneg _) hint_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hmul_nonneg]
  have hm :=
    mul_le_mul_of_nonneg_left hρ
      (Nat.cast_nonneg (analyticOrderNatAt LiCriterion.riemannXi ρ.val))
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hm

end

#print axioms weil_paired_zero_kernel_eq_quotient_v3
#print axioms riemannXi_paired_kernel_product_integral_summable_v3
