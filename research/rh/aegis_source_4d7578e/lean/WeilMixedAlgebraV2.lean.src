import WeilMixedClosureV2
import WeilThreeBlockComplexV2

/-!
Linearity and Hermitian symmetry of the ACTUAL repository arithmetic RHS.
The final theorem derives the V2 coefficient application from six explicitly
stated analytic bounds. Those six bounds are not proved by this module.
No logarithmic change of variables, global positivity, or RH is asserted.
-/
open Set Function MeasureTheory Complex
open scoped ContDiff ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilMixedClosureV2 AEGIS.WeilThreeBlockComplexV2

theorem sum_support (a b : WeilCompactSmoothGV1) :
    tsupport (fun t => a.1 t + b.1 t) ⊆ tsupport a.1 ∪ tsupport b.1 := by
  apply closure_minimal ?_ ((isClosed_tsupport _).union (isClosed_tsupport _))
  intro t ht
  by_cases ha : t ∈ tsupport a.1
  · exact Or.inl ha
  · right
    by_contra hb
    exact ht (by simp [image_eq_zero_of_notMem_tsupport ha,
      image_eq_zero_of_notMem_tsupport hb])

def addPacket (a b : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  ⟨fun t => a.1 t + b.1 t, a.2.1.add b.2.1,
    (a.2.2.1.union b.2.2.1).of_isClosed_subset (isClosed_tsupport _) (sum_support a b),
    fun x hx =>
      (sum_support a b hx).elim
        (fun ha => a.2.2.2 ha)
        (fun hb => b.2.2.2 hb)⟩

theorem scale_support (z : ℂ) (a : WeilCompactSmoothGV1) :
    tsupport (fun t => z * a.1 t) ⊆ tsupport a.1 := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro t ht
  by_contra ha
  exact ht (by simp [image_eq_zero_of_notMem_tsupport ha])

def scalePacket (z : ℂ) (a : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  ⟨fun t => z * a.1 t, contDiff_const.mul a.2.1,
    a.2.2.1.of_isClosed_subset (isClosed_tsupport _) (scale_support z a),
    (scale_support z a).trans a.2.2.2⟩

theorem mixed_add_left (a b c : WeilCompactSmoothGV1) :
    mixed (addPacket a b) c = fun x => mixed a c x + mixed b c x := by
  funext x
  change (∫ y in Ioi (0 : ℝ), (a.1 (x*y) + b.1 (x*y)) * star (c.1 y)) = _
  simp_rw [add_mul]
  exact integral_add (integrand_integrable a c x) (integrand_integrable b c x)

theorem mixed_add_right (a b c : WeilCompactSmoothGV1) :
    mixed a (addPacket b c) = fun x => mixed a b x + mixed a c x := by
  funext x
  change (∫ y in Ioi (0 : ℝ), a.1 (x*y) * star (b.1 y + c.1 y)) = _
  simp_rw [star_add, mul_add]
  exact integral_add (integrand_integrable a b x) (integrand_integrable a c x)

theorem mixed_scale_left (z : ℂ) (a b : WeilCompactSmoothGV1) :
    mixed (scalePacket z a) b = fun x => z * mixed a b x := by
  funext x
  change (∫ y in Ioi (0 : ℝ), (z * a.1 (x*y)) * star (b.1 y)) = _
  simp_rw [mul_assoc]
  exact integral_const_mul z _

theorem mixed_scale_right (z : ℂ) (a b : WeilCompactSmoothGV1) :
    mixed a (scalePacket z b) = fun x => star z * mixed a b x := by
  funext x
  change (∫ y in Ioi (0 : ℝ), a.1 (x*y) * star (z * b.1 y)) = _
  have hp : (fun y : ℝ => a.1 (x*y) * star (z * b.1 y)) =
      fun y => star z * (a.1 (x*y) * star (b.1 y)) := by
    funext y
    simp only [star_mul]
    ring
  rw [hp]
  exact integral_const_mul (star z) _

theorem prime_add (f g : ℝ → ℂ) :
    WeilPrimeTermV1 (fun x => f x + g x) =
      fun n => WeilPrimeTermV1 f n + WeilPrimeTermV1 g n := by
  funext n
  dsimp [WeilPrimeTermV1]
  ring

theorem arch_add (f g : ℝ → ℂ) :
    WeilArchimedeanIntegrandV1 (fun x => f x + g x) =
      fun x => WeilArchimedeanIntegrandV1 f x + WeilArchimedeanIntegrandV1 g x := by
  funext x
  dsimp [WeilArchimedeanIntegrandV1]
  ring

theorem prime_scale (z : ℂ) (f : ℝ → ℂ) :
    WeilPrimeTermV1 (fun x => z * f x) = fun n => z * WeilPrimeTermV1 f n := by
  funext n
  dsimp [WeilPrimeTermV1]
  ring

theorem arch_scale (z : ℂ) (f : ℝ → ℂ) :
    WeilArchimedeanIntegrandV1 (fun x => z * f x) =
      fun x => z * WeilArchimedeanIntegrandV1 f x := by
  funext x
  dsimp [WeilArchimedeanIntegrandV1]
  ring

/-- Additivity is used only with the actual convergence premises. -/
theorem rhs_add (f g : ℝ → ℂ)
    (hf : WeilExplicitRightSideConvergentV1 f)
    (hg : WeilExplicitRightSideConvergentV1 g) :
    WeilExplicitRightSideV1 (fun x => f x + g x) =
      WeilExplicitRightSideV1 f + WeilExplicitRightSideV1 g := by
  unfold WeilExplicitRightSideV1 WeilPrimeSumV1 WeilArchimedeanIntegralV1
  rw [prime_add, arch_add, hf.1.tsum_add hg.1, integral_add hf.2 hg.2]
  dsimp
  ring

theorem rhs_scale (z : ℂ) (f : ℝ → ℂ) :
    WeilExplicitRightSideV1 (fun x => z * f x) = z * WeilExplicitRightSideV1 f := by
  unfold WeilExplicitRightSideV1 WeilPrimeSumV1 WeilArchimedeanIntegralV1
  rw [prime_scale, arch_scale, tsum_mul_left, integral_const_mul]
  dsimp
  ring

def B (a b : WeilCompactSmoothGV1) : ℂ := WeilExplicitRightSideV1 (mixed a b)

theorem B_add_left (a b c : WeilCompactSmoothGV1) :
    B (addPacket a b) c = B a c + B b c := by
  unfold B
  rw [mixed_add_left]
  exact rhs_add _ _ (rhs_convergent a c) (rhs_convergent b c)

theorem B_add_right (a b c : WeilCompactSmoothGV1) :
    B a (addPacket b c) = B a b + B a c := by
  unfold B
  rw [mixed_add_right]
  exact rhs_add _ _ (rhs_convergent a b) (rhs_convergent a c)

theorem B_scale_left (z : ℂ) (a b : WeilCompactSmoothGV1) :
    B (scalePacket z a) b = z * B a b := by
  unfold B
  rw [mixed_scale_left, rhs_scale]

theorem B_scale_right (z : ℂ) (a b : WeilCompactSmoothGV1) :
    B a (scalePacket z b) = star z * B a b := by
  unfold B
  rw [mixed_scale_right, rhs_scale]

theorem reflected (f g : ℝ → ℂ)
    (h : ∀ x : ℝ, 0 < x → f x⁻¹ = (x : ℂ) * conj (g x))
    {x : ℝ} (hx : 0 < x) : (1 / (x : ℂ)) * f x⁻¹ = conj (g x) := by
  rw [h x hx]
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp [div_eq_mul_inv, ← mul_assoc, hxC]

theorem rhs_paired_conjugate (f g : ℝ → ℂ)
    (hfg : ∀ x : ℝ, 0 < x → f x⁻¹ = (x : ℂ) * conj (g x))
    (hgf : ∀ x : ℝ, 0 < x → g x⁻¹ = (x : ℂ) * conj (f x)) :
    WeilExplicitRightSideV1 g = conj (WeilExplicitRightSideV1 f) := by
  have h1 : g 1 = conj (f 1) := by simpa using hgf 1 zero_lt_one
  have hp : WeilPrimeSumV1 g = conj (WeilPrimeSumV1 f) := by
    change (∑' n : ℕ, WeilPrimeTermV1 g n) = star (∑' n : ℕ, WeilPrimeTermV1 f n)
    rw [tsum_star]
    apply tsum_congr
    intro n
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hfx : (1 / ((n + 1 : ℕ) : ℂ)) * f (((n + 1 : ℕ) : ℝ)⁻¹) =
        conj (g ((n + 1 : ℕ) : ℝ)) := by
      simpa only [Complex.ofReal_natCast] using reflected f g hfg hn
    have hgx : (1 / ((n + 1 : ℕ) : ℂ)) * g (((n + 1 : ℕ) : ℝ)⁻¹) =
        conj (f ((n + 1 : ℕ) : ℝ)) := by
      simpa only [Complex.ofReal_natCast] using reflected g f hgf hn
    simp only [WeilPrimeTermV1]
    rw [hfx, hgx]
    simp [Complex.star_def, add_comm]
  have ha : WeilArchimedeanIntegralV1 g = conj (WeilArchimedeanIntegralV1 f) := by
    unfold WeilArchimedeanIntegralV1
    rw [← integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change WeilArchimedeanIntegrandV1 g x =
      conj (WeilArchimedeanIntegrandV1 f x)
    unfold WeilArchimedeanIntegrandV1
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hfx := reflected f g hfg hx0
    have hgx := reflected g f hgf hx0
    have hxC : (x : ℂ) ≠ 0 := by
      exact_mod_cast hx0.ne'
    rw [hgx, hfx, h1]
    simp [div_eq_mul_inv, add_comm, Complex.conj_ofNat]
  simp only [WeilExplicitRightSideV1, hp, ha, h1, map_add, map_mul,
    WeilArchimedeanConstantV1, Complex.conj_ofReal]

theorem B_hermitian (a b : WeilCompactSmoothGV1) : B b a = conj (B a b) := by
  apply rhs_paired_conjugate
  · intro x hx
    exact reciprocal a b hx
  · intro x hx
    exact reciprocal b a hx

def combo (z0 z1 z2 : ℂ) (g0 g1 g2 : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  addPacket (addPacket (scalePacket z0 g0) (scalePacket z1 g1)) (scalePacket z2 g2)

/-- The exact complex coefficient expansion, with the correct conjugation and factor 2. -/
theorem actual_expansion (z0 z1 z2 : ℂ) (g0 g1 g2 : WeilCompactSmoothGV1) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (combo z0 z1 z2 g0 g1 g2))).re =
      -AEGIS.WeilThreeBlockComplexV2.diagonal z0 z1 z2
          (-(B g0 g0).re) (-(B g1 g1).re) (-(B g2 g2).re) +
        AEGIS.WeilThreeBlockComplexV2.cross z0 z1 z2
          (B g0 g1) (B g0 g2) (B g1 g2) := by
  change (B (combo z0 z1 z2 g0 g1 g2) (combo z0 z1 z2 g0 g1 g2)).re = _
  unfold combo
  simp only [B_add_left, B_add_right, B_scale_left, B_scale_right]
  rw [B_hermitian g0 g1, B_hermitian g0 g2, B_hermitian g1 g2]
  have h00im : (B g0 g0).im = 0 := by
    have h := congrArg Complex.im (B_hermitian g0 g0)
    simp only [Complex.conj_im] at h
    linarith
  have h11im : (B g1 g1).im = 0 := by
    have h := congrArg Complex.im (B_hermitian g1 g1)
    simp only [Complex.conj_im] at h
    linarith
  have h22im : (B g2 g2).im = 0 := by
    have h := congrArg Complex.im (B_hermitian g2 g2)
    simp only [Complex.conj_im] at h
    linarith
  unfold AEGIS.WeilThreeBlockComplexV2.diagonal AEGIS.WeilThreeBlockComplexV2.cross
  simp only [Complex.star_def, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply,
    h00im, h11im, h22im]
  ring

theorem actual_three_block_bound (z0 z1 z2 : ℂ) (g0 g1 g2 : WeilCompactSmoothGV1)
    (r0 r1 r2 : ℝ)
    (h0 : (103 / 100 : ℝ) * r0 ^ 2 ≤ -(B g0 g0).re)
    (h1 : (103 / 100 : ℝ) * r1 ^ 2 ≤ -(B g1 g1).re)
    (h2 : (103 / 100 : ℝ) * r2 ^ 2 ≤ -(B g2 g2).re)
    (h01 : ‖B g0 g1‖ ≤ (51 / 100 : ℝ) * r0 * r1)
    (h02 : ‖B g0 g2‖ ≤ (9 / 25 : ℝ) * r0 * r2)
    (h12 : ‖B g1 g2‖ ≤ (51 / 100 : ℝ) * r1 * r2) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (combo z0 z1 z2 g0 g1 g2))).re ≤
      -(1 / 10 : ℝ) * weightedEnergy z0 z1 z2 r0 r1 r2 := by
  rw [actual_expansion]
  exact quotient_free_margin z0 z1 z2 (B g0 g1) (B g0 g2) (B g1 g2)
    r0 r1 r2 (-(B g0 g0).re) (-(B g1 g1).re) (-(B g2 g2).re)
    h0 h1 h2 h01 h02 h12

theorem actual_combo_convergent (z0 z1 z2 : ℂ) (g0 g1 g2 : WeilCompactSmoothGV1) :
    WeilExplicitRightSideConvergentV1
      (WeilAutocorrelationV1 (combo z0 z1 z2 g0 g1 g2)) :=
  weil_autocorrelation_explicit_right_side_convergent_v1 _

end AEGIS.WeilMixedAlgebraV2
