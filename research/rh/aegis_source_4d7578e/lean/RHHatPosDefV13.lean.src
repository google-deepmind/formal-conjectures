import Mathlib

/-!
AEGIS Ω — hat kernels are positive definite against autocorrelations, V13.

For a continuous compactly supported `G : ℝ → ℂ` with autocorrelation
`C(u) = ∫ G(v+u) conj G(v) dv`, a step `h > 0` and real weights `v₀,…,v_{n-1}`,

  0 ≤ Σ_{i,j} v_i v_j ∫ Re C(u) · T_h(u − (i−j)h) du,      T_h(x) = max 0 (h − |x|).

Proof: with block averages `a_i(s) = ∫_{(0,h]} G(s + ih + t) dt`, the left side is
`∫ |Σ v_i a_i(s)|² ds` (two Fubini swaps, a translation, and the overlap length of two
intervals).  This is the positive-definiteness input for Weil-form certificates whose
kernel is a piecewise-linear interpolant of a positive-definite sequence.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory Complex
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHatPosDefV13

/-- The autocorrelation `∫ G(v+u) conj G(v) dv`. -/
def corrC (G : ℝ → ℂ) (u : ℝ) : ℂ := ∫ v, G (v + u) * conj (G v)

/-- The hat function of half-width `h`. -/
def hatT (h x : ℝ) : ℝ := max 0 (h - |x|)

/-- Block average `∫_{(0,h]} G(s + c + t) dt`. -/
def block (G : ℝ → ℂ) (h c s : ℝ) : ℂ := ∫ t in Ioc (0 : ℝ) h, G (s + c + t)

theorem integrable_norm_mul_const (f : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (M h : ℝ) :
    Integrable (fun z : ℝ × ℝ => ‖f z.1‖ * M) (volume.prod (volume.restrict (Ioc (0 : ℝ) h))) := by
  have h1 : Integrable (fun x : ℝ => ‖f x‖) volume :=
    (hf.integrable_of_hasCompactSupport hfc).norm
  have h2 : Integrable (fun _ : ℝ => M) (volume.restrict (Ioc (0 : ℝ) h)) :=
    integrable_const M
  exact h1.mul_prod h2

theorem overlap_length (h x : ℝ) (hh : 0 ≤ h) :
    volume.real (Ioc x (x + h) ∩ Ioc 0 h) = hatT h x := by
  have e : Ioc x (x + h) ∩ Ioc 0 h = Ioc (max x 0) (min (x + h) h) := by
    ext y; simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]; tauto
  rw [e, Real.volume_real_Ioc]
  unfold hatT
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, min_eq_right (by linarith), abs_of_nonneg hx, max_comm]
  · rw [max_eq_right hx, min_eq_left (by linarith), abs_of_nonpos hx, max_comm]
    congr 1; ring

section Generic
variable (G : ℝ → ℂ) (hG : Continuous G) (hGc : HasCompactSupport G)
include hG hGc

omit hG in
theorem exists_zero_outside : ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R < |x| → G x = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hGc.isCompact.isBounded
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith [le_max_left R 0]

theorem exists_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, ‖G x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hG.bounded_above_of_compact_support hGc
  exact ⟨max M 0, le_max_right _ _, fun x => le_trans (hM x) (le_max_left _ _)⟩

omit hGc in
theorem block_continuous (h c : ℝ) (hh : 0 ≤ h) : Continuous (block G h c) := by
  have : block G h c = fun s => ∫ t in (0 : ℝ)..h, G (s + c + t) := by
    funext s
    rw [intervalIntegral.integral_of_le hh]
    rfl
  rw [this]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hG.comp (by fun_prop)

theorem block_zero_outside (h c : ℝ) (hh : 0 ≤ h) :
    ∃ R : ℝ, ∀ s : ℝ, R < |s| → block G h c s = 0 := by
  obtain ⟨R, hR0, hR⟩ := exists_zero_outside G hGc
  refine ⟨R + |c| + h, fun s hs => ?_⟩
  unfold block
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  apply hR
  have h1 : |s| ≤ |s + c + t| + |c| + |t| := by
    have := abs_sub (s + c + t) (c + t)
    have h2 : s + c + t - (c + t) = s := by ring
    rw [h2] at this
    linarith [abs_add_le c t]
  have h3 : |t| ≤ h := by rw [abs_of_pos ht.1]; exact ht.2
  linarith

theorem block_hasCompactSupport (h c : ℝ) (hh : 0 ≤ h) : HasCompactSupport (block G h c) := by
  obtain ⟨R, hR⟩ := block_zero_outside G hG hGc h c hh
  set R' := max R 0 with hR'
  have hR0 : 0 ≤ R' := le_max_right _ _
  have hRR : R ≤ R' := le_max_left _ _
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-R') R'))
  intro s hs
  apply hR
  rw [mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with hs | hs
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem fubini_one (h c₁ c₂ : ℝ) (hh : 0 ≤ h) :
    (∫ s, ∫ t' in Ioc (0 : ℝ) h, block G h c₁ s * conj (G (s + c₂ + t'))) =
      ∫ t' in Ioc (0 : ℝ) h, ∫ s, block G h c₁ s * conj (G (s + c₂ + t')) := by
  apply integral_integral_swap
  obtain ⟨M, hM0, hM⟩ := exists_bound G hG hGc
  have hb := block_continuous G hG h c₁ hh
  have hbc := block_hasCompactSupport G hG hGc h c₁ hh
  refine (integrable_norm_mul_const _ hb hbc M h).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact (hb.comp continuous_fst).mul
      (continuous_conj.comp (hG.comp (by fun_prop)))
  · refine Filter.Eventually.of_forall (fun z => ?_)
    simp only [Function.uncurry, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)

theorem fubini_two (h d : ℝ) :
    (∫ y, ∫ t in Ioc (0 : ℝ) h, G (y + (d + t)) * conj (G y)) =
      ∫ t in Ioc (0 : ℝ) h, ∫ y, G (y + (d + t)) * conj (G y) := by
  apply integral_integral_swap
  obtain ⟨M, hM0, hM⟩ := exists_bound G hG hGc
  have hi : Integrable (fun z : ℝ × ℝ => ‖conj (G z.1)‖ * M)
      (volume.prod (volume.restrict (Ioc (0 : ℝ) h))) :=
    integrable_norm_mul_const _ (continuous_conj.comp hG) (hGc.comp_left (by simp)) M h
  refine hi.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact (hG.comp (by fun_prop)).mul (continuous_conj.comp (hG.comp continuous_fst))
  · refine Filter.Eventually.of_forall (fun z => ?_)
    simp only [Function.uncurry, norm_mul, Complex.norm_conj]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)

theorem block_pair (h c₁ c₂ : ℝ) (hh : 0 ≤ h) :
    (∫ s, block G h c₁ s * conj (block G h c₂ s)) =
      ∫ t' in Ioc (0 : ℝ) h, ∫ t in Ioc (0 : ℝ) h, corrC G (c₁ - c₂ + t - t') := by
  have step1 : ∀ s, block G h c₁ s * conj (block G h c₂ s) =
      ∫ t' in Ioc (0 : ℝ) h, block G h c₁ s * conj (G (s + c₂ + t')) := by
    intro s
    unfold block
    rw [← integral_conj, ← integral_const_mul]
  simp_rw [step1]
  rw [fubini_one G hG hGc h c₁ c₂ hh]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t' _
  beta_reduce
  have htr := integral_sub_right_eq_self (μ := volume)
    (fun s => block G h c₁ s * conj (G (s + c₂ + t'))) (c₂ + t')
  rw [← htr]
  have step2 : ∀ y, block G h c₁ (y - (c₂ + t')) * conj (G (y - (c₂ + t') + c₂ + t')) =
      ∫ t in Ioc (0 : ℝ) h, G (y + (c₁ - c₂ - t' + t)) * conj (G y) := by
    intro y
    unfold block
    rw [← integral_mul_const]
    have e1 : y - (c₂ + t') + c₂ + t' = y := by ring
    rw [e1]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    beta_reduce
    have e2 : y - (c₂ + t') + c₁ + t = y + (c₁ - c₂ - t' + t) := by ring
    rw [e2]
  simp_rw [step2]
  rw [fubini_two G hG hGc h (c₁ - c₂ - t')]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  beta_reduce
  unfold corrC
  have e3 : c₁ - c₂ - t' + t = c₁ - c₂ + t - t' := by ring
  rw [e3]

theorem corrC_zero_outside : ∃ R : ℝ, ∀ u : ℝ, R < |u| → corrC G u = 0 := by
  obtain ⟨R, hR0, hR⟩ := exists_zero_outside G hGc
  refine ⟨2 * R, fun u hu => ?_⟩
  unfold corrC
  apply integral_eq_zero_of_ae
  refine Filter.Eventually.of_forall (fun v => ?_)
  by_cases hv : R < |v|
  · simp [hR v hv]
  · have : R < |v + u| := by
      have := abs_sub (v + u) v
      have e : v + u - v = u := by ring
      rw [e] at this
      push Not at hv
      linarith
    simp [hR _ this]

theorem corrC_hasCompactSupport : HasCompactSupport (corrC G) := by
  obtain ⟨R, hR⟩ := corrC_zero_outside G hG hGc
  set R' := max R 0 with hR'
  have hR0 : 0 ≤ R' := le_max_right _ _
  have hRR : R ≤ R' := le_max_left _ _
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-R') R'))
  intro s hs
  apply hR
  rw [mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with hs | hs
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem hat_overlap (h d : ℝ) (hh : 0 ≤ h) (hC : Continuous (corrC G)) :
    (∫ t' in Ioc (0 : ℝ) h, ∫ t in Ioc (0 : ℝ) h, corrC G (d + t - t')) =
      ∫ u, corrC G u * (hatT h (u - d) : ℂ) := by
  set C := corrC G with hCdef
  have hCi : Integrable C := hC.integrable_of_hasCompactSupport (corrC_hasCompactSupport G hG hGc)
  -- inner substitution
  have inner : ∀ t', (∫ t in Ioc (0 : ℝ) h, C (d + t - t')) =
      ∫ u, (Ioc (d - t') (d - t' + h)).indicator C u := by
    intro t'
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hh,
      ← intervalIntegral.integral_of_le (by linarith)]
    have := intervalIntegral.integral_comp_add_right (a := 0) (b := h) C (d - t')
    rw [zero_add, add_comm h (d - t')] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    congr 1; ring
  simp_rw [inner]
  -- swap
  set S : Set (ℝ × ℝ) := {p | d - p.1 < p.2 ∧ p.2 ≤ d - p.1 + h} with hS
  have hSm : MeasurableSet S := by
    show MeasurableSet ({p : ℝ × ℝ | d - p.1 < p.2} ∩ {p : ℝ × ℝ | p.2 ≤ d - p.1 + h})
    exact (measurableSet_lt (measurable_const.sub measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd ((measurable_const.sub measurable_fst).add_const h))
  have hswap := integral_integral_swap (μ := volume.restrict (Ioc (0 : ℝ) h)) (ν := volume)
    (f := fun t' u => S.indicator (fun p : ℝ × ℝ => C p.2) (t', u)) ?_
  · have e1 : ∀ t' u, (Ioc (d - t') (d - t' + h)).indicator C u =
        S.indicator (fun p : ℝ × ℝ => C p.2) (t', u) := by
      intro t' u
      by_cases hm : u ∈ Ioc (d - t') (d - t' + h)
      · rw [indicator_of_mem hm, indicator_of_mem (show (t', u) ∈ S from hm)]
      · rw [indicator_of_notMem hm, indicator_of_notMem (show (t', u) ∉ S from hm)]
    simp_rw [e1]
    rw [hswap]
    congr 1
    funext u
    have e2 : ∀ t', S.indicator (fun p : ℝ × ℝ => C p.2) (t', u) =
        (Ioc (d - u) (d - u + h)).indicator (fun _ => C u) t' := by
      intro t'
      have hiff : (t', u) ∈ S ↔ t' ∈ Ioc (d - u) (d - u + h) := by
        simp only [hS, Set.mem_ofPred_eq, mem_Ioc]
        constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith
      by_cases hm : t' ∈ Ioc (d - u) (d - u + h)
      · rw [indicator_of_mem hm, indicator_of_mem (hiff.mpr hm)]
      · rw [indicator_of_notMem hm, indicator_of_notMem (fun h' => hm (hiff.mp h'))]
    simp_rw [e2]
    rw [integral_indicator_const _ measurableSet_Ioc, measureReal_restrict_apply measurableSet_Ioc,
      overlap_length h (d - u) hh, Complex.real_smul, mul_comm]
    unfold hatT
    rw [abs_sub_comm]
  · have hb : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * ‖C z.2‖)
        ((volume.restrict (Ioc (0 : ℝ) h)).prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod hCi.norm
    refine hb.mono' ?_ ?_
    · exact ((hC.comp continuous_snd).aestronglyMeasurable).indicator hSm
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, one_mul]
      by_cases hz : z ∈ S
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz, norm_zero]; exact norm_nonneg _

theorem pair_eq_hat (h c₁ c₂ : ℝ) (hh : 0 ≤ h) (hC : Continuous (corrC G)) :
    (∫ s, block G h c₁ s * conj (block G h c₂ s)).re =
      ∫ u, (corrC G u).re * hatT h (u - (c₁ - c₂)) := by
  rw [block_pair G hG hGc h c₁ c₂ hh, hat_overlap G hG hGc h (c₁ - c₂) hh hC]
  have hCi : Integrable (corrC G) :=
    hC.integrable_of_hasCompactSupport (corrC_hasCompactSupport G hG hGc)
  have hI : Integrable (fun u => corrC G u * (hatT h (u - (c₁ - c₂)) : ℂ)) := by
    refine (hCi.norm.mul_const h).mono' ?_ ?_
    · exact (hC.mul (Complex.continuous_ofReal.comp
        (by unfold hatT; fun_prop))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun u => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      unfold hatT
      rw [abs_of_nonneg (le_max_left _ _)]
      apply max_le hh
      linarith [abs_nonneg (u - (c₁ - c₂))]
  have hre := (integral_re hI).symm
  simp only [RCLike.re_to_complex] at hre
  rw [hre]
  congr 1
  funext u
  rw [Complex.re_mul_ofReal]

/-- **Hat kernels are positive definite.** -/
theorem hat_posdef (h : ℝ) (hh : 0 ≤ h) (hC : Continuous (corrC G)) (n : ℕ) (v : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      v i * v j * ∫ u, (corrC G u).re * hatT h (u - ((i : ℝ) - j) * h) := by
  set a : ℕ → ℝ → ℂ := fun i => block G h ((i : ℝ) * h) with ha
  have hcont : ∀ i, Continuous (a i) := fun i => block_continuous G hG h _ hh
  have hsupp : ∀ i, HasCompactSupport (a i) := fun i => block_hasCompactSupport G hG hGc h _ hh
  have hint : ∀ i j, Integrable (fun s => a i s * conj (a j s)) := by
    intro i j
    exact ((hcont i).mul (continuous_conj.comp (hcont j))).integrable_of_hasCompactSupport
      ((hsupp i).mul_right)
  have key : ∀ i j : ℕ, ∫ u, (corrC G u).re * hatT h (u - ((i : ℝ) - j) * h) =
      (∫ s, a i s * conj (a j s)).re := by
    intro i j
    rw [ha]
    simp only
    rw [pair_eq_hat G hG hGc h _ _ hh hC]
    congr 1; funext u; congr 2; ring
  simp_rw [key]
  set F : ℝ → ℂ := fun s => ∑ i ∈ Finset.range n, (v i : ℂ) * a i s with hF
  have hexp : ∀ s, F s * conj (F s) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        ((v i * v j : ℝ) : ℂ) * (a i s * conj (a j s)) := by
    intro s
    rw [hF]
    simp only
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [map_mul, Complex.conj_ofReal]
    push_cast; ring
  have hint2 : ∀ i j, Integrable (fun s => ((v i * v j : ℝ) : ℂ) * (a i s * conj (a j s))) :=
    fun i j => (hint i j).const_mul _
  have htot : (∫ s, F s * conj (F s)) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        ((v i * v j : ℝ) : ℂ) * ∫ s, a i s * conj (a j s) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint2 i j))]
    apply Finset.sum_congr rfl; intro i _
    rw [integral_finsetSum _ (fun j _ => hint2 i j)]
    apply Finset.sum_congr rfl; intro j _
    rw [integral_const_mul]
  have hnn : 0 ≤ (∫ s, F s * conj (F s)).re := by
    have e : ∀ s, F s * conj (F s) = ((Complex.normSq (F s) : ℝ) : ℂ) := fun s =>
      Complex.mul_conj (F s)
    simp_rw [e]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    exact integral_nonneg (fun s => Complex.normSq_nonneg _)
  rw [htot, Complex.re_sum] at hnn
  convert hnn using 2 with i _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [Complex.re_ofReal_mul]

omit hG hGc in
theorem corrC_neg (u : ℝ) : corrC G (-u) = conj (corrC G u) := by
  unfold corrC
  rw [← integral_conj]
  have := integral_add_right_eq_self (μ := volume) (fun x => G (x + -u) * conj (G x)) u
  rw [← this]
  congr 1
  funext x
  rw [map_mul, Complex.conj_conj, mul_comm]
  congr 2; ring_nf

theorem re_corr_hat_integrable (h d : ℝ) (hC : Continuous (corrC G)) :
    Integrable (fun u => (corrC G u).re * hatT h (u - d)) := by
  have hCi : Integrable (corrC G) :=
    hC.integrable_of_hasCompactSupport (corrC_hasCompactSupport G hG hGc)
  refine (hCi.norm.mul_const (max 0 h)).mono' ?_ ?_
  · exact ((Complex.continuous_re.comp hC).mul (by unfold hatT; fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun u => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    apply mul_le_mul (Complex.abs_re_le_norm _) _ (abs_nonneg _) (norm_nonneg _)
    unfold hatT
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le_max le_rfl (by linarith [abs_nonneg (u - d)])

theorem fold_half (h d : ℝ) (hC : Continuous (corrC G)) :
    (∫ u, (corrC G u).re * hatT h (u - d)) =
      (∫ u in Ioi (0 : ℝ), (corrC G u).re * hatT h (u - d)) +
        ∫ u in Ioi (0 : ℝ), (corrC G u).re * hatT h (u - -d) := by
  have hI := re_corr_hat_integrable G hG hGc h d hC
  rw [← intervalIntegral.integral_Iic_add_Ioi hI.integrableOn hI.integrableOn, add_comm]
  congr 1
  have e := integral_comp_neg_Ioi (0 : ℝ) (fun u => (corrC G u).re * hatT h (u - d))
  rw [neg_zero] at e
  rw [← e]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only
  rw [corrC_neg G u, Complex.conj_re]
  unfold hatT
  congr 2
  rw [show -u - d = -(u - -d) by ring, abs_neg]

/-- **Hat kernels are positive definite on the half-line.** -/
theorem hat_posdef_Ioi (h : ℝ) (hh : 0 ≤ h) (hC : Continuous (corrC G)) (n : ℕ) (v : ℕ → ℝ) :
    0 ≤ ∫ u in Ioi (0 : ℝ), (corrC G u).re *
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * hatT h (u - ((i : ℝ) - j) * h) := by
  have hp := hat_posdef G hG hGc h hh hC n v
  set J : ℝ → ℝ := fun d => ∫ u in Ioi (0 : ℝ), (corrC G u).re * hatT h (u - d) with hJ
  have hsplit : ∀ i j : ℕ, (∫ u, (corrC G u).re * hatT h (u - ((i : ℝ) - j) * h)) =
      J (((i : ℝ) - j) * h) + J (((j : ℝ) - i) * h) := by
    intro i j
    rw [fold_half G hG hGc h _ hC, hJ]
    simp only
    congr 3; funext u; congr 2; ring
  simp_rw [hsplit, mul_add, Finset.sum_add_distrib] at hp
  have hswap : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * J (((j : ℝ) - i) * h)) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * J (((i : ℝ) - j) * h) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hswap] at hp
  have hint : ∀ i j : ℕ, IntegrableOn
      (fun u => v i * v j * ((corrC G u).re * hatT h (u - ((i : ℝ) - j) * h))) (Ioi (0 : ℝ)) :=
    fun i j => ((re_corr_hat_integrable G hG hGc h _ hC).const_mul _).integrableOn
  have heq : (∫ u in Ioi (0 : ℝ), (corrC G u).re *
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * hatT h (u - ((i : ℝ) - j) * h)) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * J (((i : ℝ) - j) * h) := by
    have e : ∀ u, (corrC G u).re *
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * hatT h (u - ((i : ℝ) - j) * h) =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          v i * v j * ((corrC G u).re * hatT h (u - ((i : ℝ) - j) * h)) := by
      intro u
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      ring
    simp_rw [e]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    apply Finset.sum_congr rfl; intro i _
    rw [integral_finsetSum _ (fun j _ => hint i j)]
    apply Finset.sum_congr rfl; intro j _
    rw [integral_const_mul]
  rw [heq]
  linarith

end Generic

end AEGIS.RHHatPosDefV13
