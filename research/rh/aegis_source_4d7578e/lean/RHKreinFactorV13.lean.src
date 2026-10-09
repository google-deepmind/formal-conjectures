import Mathlib

/-!
AEGIS Ω — the moment-zero factorisation for the Krein dual certificate, V13.

In the logarithmic coordinate the two Weil moment conditions are `∫ G(y)·e^{±y/2} dy = 0`.
Put `G₁ = e^{−|·|/2} * G`, the Green's function of `1/4 − D²` applied to `G`, so that
`Ĝ₁(ξ) = Ĝ(ξ)/(ξ² + 1/4)`. If `G` vanishes outside `[a, b]` and both moments are zero, then
`G₁` also vanishes outside `[a, b]`. The reason is that on `x ≥ b` the kernel factors as
`e^{−x/2}·e^{y/2}`, and on `x ≤ a` as `e^{x/2}·e^{−y/2}`.

`kreinFactor_lift_support` states the same for the unitary log lift `G(t) = e^{t/2}·g(e^t)` of a
multiplicative `g` supported in `[e^a, e^b]`, under the repository's moment conditions
`∫_{x>0} g(x)/x dx = 0` and `∫_{x>0} g(x) dx = 0` (the two halves of `WeilMomentConditionsV1`).

The second half is the differential equation. `G1 = e^{−x/2}·∫_a^x e^{y/2}G − e^{x/2}·∫_b^x e^{−y/2}G` is
twice differentiable with `G1/4 − G1'' = G` (`G1_ode`, fundamental theorem of calculus). It vanishes outside
`(a, b)` when both interval moments are zero (`G1_support`). `G1_lift` states both facts for the log lift of a
repository test function under `WeilMomentConditionsV1`.

Together these give the factorisation `g = (1/4 − D²)g₁` with `g₁` supported in the same interval. The
Fourier-side certificate in `RH_STATUS.md` uses it.

`moment_zero_parametrization` is the smooth form. If `h` is `C^∞` with `tsupport h ⊆ [a, b]` and
`∫ e^{±u/2} h(u) du = 0`, then `h = χ'' − χ/4` with `χ = −G1` smooth and `tsupport χ ⊆ [a, b]`. `G1` is the
composition of the first-order inverses of `D + 1/2` and `D − 1/2`. Not RH. AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinFactorV13

/-- `G₁(x) = ∫ e^{−|x − y|/2}·G(y) dy`. -/
def kreinFactor (G : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, (Real.exp (-(|x - y|) / 2) : ℂ) * G y

theorem kreinFactor_eq_zero_of_le (G : ℝ → ℂ) (a b : ℝ)
    (hsupp : ∀ y, G y ≠ 0 → y ∈ Icc a b)
    (hmom : ∫ y, (Real.exp (y / 2) : ℂ) * G y = 0) {x : ℝ} (hx : b ≤ x) :
    kreinFactor G x = 0 := by
  have hpt : ∀ y, (Real.exp (-(|x - y|) / 2) : ℂ) * G y =
      (Real.exp (-x / 2) : ℂ) * ((Real.exp (y / 2) : ℂ) * G y) := by
    intro y
    by_cases hG : G y = 0
    · simp [hG]
    · have hy : y ≤ x := le_trans (hsupp y hG).2 hx
      have habs : |x - y| = x - y := abs_of_nonneg (by linarith)
      rw [habs, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 3
      ring
  unfold kreinFactor
  simp_rw [hpt]
  rw [integral_const_mul, hmom, mul_zero]

theorem kreinFactor_eq_zero_of_ge (G : ℝ → ℂ) (a b : ℝ)
    (hsupp : ∀ y, G y ≠ 0 → y ∈ Icc a b)
    (hmom : ∫ y, (Real.exp (-y / 2) : ℂ) * G y = 0) {x : ℝ} (hx : x ≤ a) :
    kreinFactor G x = 0 := by
  have hpt : ∀ y, (Real.exp (-(|x - y|) / 2) : ℂ) * G y =
      (Real.exp (x / 2) : ℂ) * ((Real.exp (-y / 2) : ℂ) * G y) := by
    intro y
    by_cases hG : G y = 0
    · simp [hG]
    · have hy : x ≤ y := le_trans hx (hsupp y hG).1
      have habs : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      rw [habs, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 3
      ring
  unfold kreinFactor
  simp_rw [hpt]
  rw [integral_const_mul, hmom, mul_zero]

/-- Both moments zero and `G` supported in `[a, b]`: `G₁ = e^{−|·|/2} * G` is supported in `[a, b]`. -/
theorem kreinFactor_support (G : ℝ → ℂ) (a b : ℝ)
    (hsupp : ∀ y, G y ≠ 0 → y ∈ Icc a b)
    (hplus : ∫ y, (Real.exp (y / 2) : ℂ) * G y = 0)
    (hminus : ∫ y, (Real.exp (-y / 2) : ℂ) * G y = 0) :
    ∀ x, kreinFactor G x ≠ 0 → x ∈ Ioo a b := by
  intro x hx
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hx (kreinFactor_eq_zero_of_ge G a b hsupp hminus (not_lt.mp h))
  · by_contra h
    exact hx (kreinFactor_eq_zero_of_le G a b hsupp hplus (not_lt.mp h))

/-- The unitary log lift `G(t) = e^{t/2}·g(e^t)` (same as `WeilLogCoordinateIsometryV21.logLift`). -/
def lift (g : ℝ → ℂ) (t : ℝ) : ℂ := (Real.exp (t / 2) : ℂ) * g (Real.exp t)

/-- Whole-line exponential substitution for complex-valued integrands. -/
theorem integral_exp_subst (f : ℝ → ℂ) :
    (∫ t : ℝ, (Real.exp t : ℂ) * f (Real.exp t)) = ∫ x in Ioi (0 : ℝ), f x := by
  have hcov :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (f := Real.exp) (f' := Real.exp) (s := Set.univ) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (Set.injOn_of_injective Real.exp_injective) f
  rw [Set.image_univ, Real.range_exp] at hcov
  rw [hcov, Measure.restrict_univ]
  congr 1
  funext t
  rw [abs_of_pos (Real.exp_pos t), Complex.real_smul]

/-- `∫ e^{t/2}·G(t) dt = ∫_{x>0} g(x) dx`. -/
theorem lift_moment_plus (g : ℝ → ℂ) :
    (∫ t, (Real.exp (t / 2) : ℂ) * lift g t) = ∫ x in Ioi (0 : ℝ), g x := by
  rw [← integral_exp_subst]
  congr 1
  funext t
  unfold lift
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

/-- `∫ e^{−t/2}·G(t) dt = ∫_{x>0} g(x)/x dx`. -/
theorem lift_moment_minus (g : ℝ → ℂ) :
    (∫ t, (Real.exp (-t / 2) : ℂ) * lift g t) = ∫ x in Ioi (0 : ℝ), g x / (x : ℂ) := by
  rw [← integral_exp_subst]
  congr 1
  funext t
  unfold lift
  have hne : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  have h0 : -t / 2 + t / 2 = 0 := by ring
  rw [h0, Real.exp_zero, Complex.ofReal_one, one_mul]
  field_simp

/-- The repository's two moment conditions, for `g` supported in `[e^a, e^b]`, make
`e^{−|·|/2} * G` vanish outside `(a, b)`, where `G` is the unitary log lift of `g`. -/
theorem kreinFactor_lift_support (g : ℝ → ℂ) (a b : ℝ)
    (hsupp : ∀ x, g x ≠ 0 → x ∈ Icc (Real.exp a) (Real.exp b))
    (hinv : ∫ x in Ioi (0 : ℝ), g x / (x : ℂ) = 0)
    (hone : ∫ x in Ioi (0 : ℝ), g x = 0) :
    ∀ t, kreinFactor (lift g) t ≠ 0 → t ∈ Ioo a b := by
  refine kreinFactor_support (lift g) a b ?_ (by rw [lift_moment_plus]; exact hone)
    (by rw [lift_moment_minus]; exact hinv)
  intro t ht
  have hg : g (Real.exp t) ≠ 0 := by
    intro h0; apply ht; simp [lift, h0]
  have hmem := hsupp _ hg
  exact ⟨Real.exp_le_exp.mp hmem.1, Real.exp_le_exp.mp hmem.2⟩

/-- `e^{c·x}` as a complex-valued function of a real variable. -/
def ex (c : ℝ) (x : ℝ) : ℂ := (Real.exp (c * x) : ℂ)

theorem hasDerivAt_ex (c x : ℝ) : HasDerivAt (ex c) (c * ex c x) x := by
  have h : HasDerivAt (fun y => Real.exp (c * y)) (Real.exp (c * x) * c) x := by
    have h0 := ((hasDerivAt_id x).const_mul c).exp
    simpa using h0
  have h2 : HasDerivAt (fun y => ((Real.exp (c * y) : ℝ) : ℂ)) ((Real.exp (c * x) * c : ℝ) : ℂ) x :=
    h.ofReal_comp
  exact h2.congr_deriv (by unfold ex; push_cast; ring)

/-- `P(x) = ∫_a^x e^{y/2} G(y) dy`. -/
def P (G : ℝ → ℂ) (a x : ℝ) : ℂ := ∫ y in a..x, ex (1/2) y * G y
/-- `Q(x) = ∫_b^x e^{−y/2} G(y) dy`. -/
def Q (G : ℝ → ℂ) (b x : ℝ) : ℂ := ∫ y in b..x, ex (-1/2) y * G y

/-- `G₁ = e^{−x/2}·P − e^{x/2}·Q`. -/
def G1 (G : ℝ → ℂ) (a b x : ℝ) : ℂ := ex (-1/2) x * P G a x - ex (1/2) x * Q G b x

/-- `G₁' = −½·e^{−x/2}·P − ½·e^{x/2}·Q`. -/
def G1' (G : ℝ → ℂ) (a b x : ℝ) : ℂ :=
  -(1/2 : ℂ) * ex (-1/2) x * P G a x - (1/2 : ℂ) * ex (1/2) x * Q G b x

theorem ex_mul_ex (c d x : ℝ) : ex c x * ex d x = ex (c + d) x := by
  unfold ex; rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring

theorem hasDerivAt_P (G : ℝ → ℂ) (hG : Continuous G) (a x : ℝ) :
    HasDerivAt (P G a) (ex (1/2) x * G x) x := by
  have hc : Continuous (fun y => ex (1/2) y * G y) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul hG
  exact (hc.integral_hasStrictDerivAt a x).hasDerivAt

theorem hasDerivAt_Q (G : ℝ → ℂ) (hG : Continuous G) (b x : ℝ) :
    HasDerivAt (Q G b) (ex (-1/2) x * G x) x := by
  have hc : Continuous (fun y => ex (-1/2) y * G y) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul hG
  exact (hc.integral_hasStrictDerivAt b x).hasDerivAt

theorem hasDerivAt_G1 (G : ℝ → ℂ) (hG : Continuous G) (a b x : ℝ) :
    HasDerivAt (G1 G a b) (G1' G a b x) x := by
  have h1 := (hasDerivAt_ex (-1/2) x).mul (hasDerivAt_P G hG a x)
  have h2 := (hasDerivAt_ex (1/2) x).mul (hasDerivAt_Q G hG b x)
  have e1 : ex (-1/2) x * (ex (1/2) x * G x) = G x := by
    rw [← mul_assoc, ex_mul_ex]; norm_num [ex]
  have e2 : ex (1/2) x * (ex (-1/2) x * G x) = G x := by
    rw [← mul_assoc, ex_mul_ex]; norm_num [ex]
  exact (h1.sub h2).congr_deriv (by unfold G1'; push_cast; linear_combination e1 - e2)

theorem hasDerivAt_G1' (G : ℝ → ℂ) (hG : Continuous G) (a b x : ℝ) :
    HasDerivAt (G1' G a b) (G1 G a b x / 4 - G x) x := by
  have h1 := ((hasDerivAt_ex (-1/2) x).const_mul (-(1/2 : ℂ))).mul (hasDerivAt_P G hG a x)
  have h2 := ((hasDerivAt_ex (1/2) x).const_mul (1/2 : ℂ)).mul (hasDerivAt_Q G hG b x)
  have e1 : ex (-1/2) x * (ex (1/2) x * G x) = G x := by
    rw [← mul_assoc, ex_mul_ex]; norm_num [ex]
  have e2 : ex (1/2) x * (ex (-1/2) x * G x) = G x := by
    rw [← mul_assoc, ex_mul_ex]; norm_num [ex]
  exact (h1.sub h2).congr_deriv (by
    unfold G1; push_cast; linear_combination (-(1/2 : ℂ)) * e1 - (1/2 : ℂ) * e2)

/-- `(1/4 − D²) G₁ = G`: `G₁` is twice differentiable and `G₁/4 − G₁'' = G`. -/
theorem G1_ode (G : ℝ → ℂ) (hG : Continuous G) (a b x : ℝ) :
    deriv (G1 G a b) = G1' G a b ∧ G1 G a b x / 4 - deriv (G1' G a b) x = G x := by
  refine ⟨funext fun y => (hasDerivAt_G1 G hG a b y).deriv, ?_⟩
  rw [(hasDerivAt_G1' G hG a b x).deriv]; ring

theorem continuous_ex (c : ℝ) : Continuous (ex c) :=
  Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))

theorem integral_zero_right (f : ℝ → ℂ) (b x : ℝ) (hbx : b ≤ x)
    (hf : ∀ y, b < y → f y = 0) : (∫ y in b..x, f y) = 0 := by
  rw [intervalIntegral.integral_of_le hbx]
  rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℂ)) (fun y hy => hf y hy.1)]
  simp

theorem integral_zero_left (f : ℝ → ℂ) (a x : ℝ) (hxa : x ≤ a)
    (hf : ∀ y, y ≤ a → f y = 0) : (∫ y in a..x, f y) = 0 := by
  rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hxa]
  rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℂ)) (fun y hy => hf y hy.2)]
  simp

/-- With `G` continuous, vanishing outside `(a, b)`, and both interval moments zero,
`G₁ = e^{−x/2}·P − e^{x/2}·Q` vanishes outside `(a, b)`. -/
theorem G1_support (G : ℝ → ℂ) (hG : Continuous G) (a b : ℝ)
    (hsupp : ∀ y, G y ≠ 0 → y ∈ Ioo a b)
    (hplus : (∫ y in a..b, ex (1/2) y * G y) = 0)
    (hminus : (∫ y in a..b, ex (-1/2) y * G y) = 0) :
    ∀ x, G1 G a b x ≠ 0 → x ∈ Ioo a b := by
  have hz : ∀ y, y ∉ Ioo a b → G y = 0 := fun y hy => by
    by_contra h; exact hy (hsupp y h)
  have hii : ∀ c u v, IntervalIntegrable (fun y => ex c y * G y) volume u v :=
    fun c u v => ((continuous_ex c).mul hG).intervalIntegrable u v
  intro x hx
  by_contra hout
  apply hx
  rcases not_and_or.mp hout with h | h
  · -- x ≤ a
    have hxa : x ≤ a := not_lt.mp h
    have hP : P G a x = 0 := integral_zero_left _ a x hxa
      (fun y hy => by rw [hz y (fun hm => absurd hm.1 (not_lt.mpr hy)), mul_zero])
    have hQ : Q G b x = 0 := by
      unfold Q
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii _ b a) (hii _ a x),
        intervalIntegral.integral_symm, hminus, neg_zero, zero_add]
      exact integral_zero_left _ a x hxa
        (fun y hy => by rw [hz y (fun hm => absurd hm.1 (not_lt.mpr hy)), mul_zero])
    simp [G1, hP, hQ]
  · -- b ≤ x
    have hbx : b ≤ x := not_lt.mp h
    have hQ : Q G b x = 0 := integral_zero_right _ b x hbx
      (fun y hy => by rw [hz y (fun hm => absurd hm.2 (not_lt.mpr hy.le)), mul_zero])
    have hP : P G a x = 0 := by
      unfold P
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii _ a b) (hii _ b x), hplus, zero_add]
      exact integral_zero_right _ b x hbx
        (fun y hy => by rw [hz y (fun hm => absurd hm.2 (not_lt.mpr hy.le)), mul_zero])
    simp [G1, hP, hQ]

theorem interval_eq_whole (f : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hf : ∀ y, y ∉ Ioo a b → f y = 0) : (∫ y in a..b, f y) = ∫ y, f y := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy => hf y (fun h => hy ⟨h.1, h.2.le⟩))

/-- The factorisation for the repository's test functions: if `g` is continuous, its unitary
log lift `G` vanishes outside `(a, b)`, and `∫_{x>0} g(x)/x dx = ∫_{x>0} g(x) dx = 0`, then
`G₁ = e^{−x/2}·∫_a^x e^{y/2}G − e^{x/2}·∫_b^x e^{−y/2}G` vanishes outside `(a, b)` and solves
`G₁/4 − G₁'' = G`. -/
theorem G1_lift (g : ℝ → ℂ) (hg : Continuous g) (a b : ℝ) (hab : a ≤ b)
    (hsupp : ∀ t, lift g t ≠ 0 → t ∈ Ioo a b)
    (hinv : ∫ x in Ioi (0 : ℝ), g x / (x : ℂ) = 0)
    (hone : ∫ x in Ioi (0 : ℝ), g x = 0) :
    (∀ x, G1 (lift g) a b x ≠ 0 → x ∈ Ioo a b) ∧
      ∀ x, G1 (lift g) a b x / 4 - deriv (G1' (lift g) a b) x = lift g x := by
  have hG : Continuous (lift g) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2))).mul
      (hg.comp Real.continuous_exp)
  have hz : ∀ c y, y ∉ Ioo a b → ex c y * lift g y = 0 := fun c y hy => by
    have : lift g y = 0 := by by_contra h; exact hy (hsupp y h)
    rw [this, mul_zero]
  have hplus : (∫ y in a..b, ex (1/2) y * lift g y) = 0 := by
    rw [interval_eq_whole _ a b hab (hz _), ← hone, ← lift_moment_plus]
    congr 1; funext y; unfold ex; rw [show (1/2 : ℝ) * y = y / 2 by ring]
  have hminus : (∫ y in a..b, ex (-1/2) y * lift g y) = 0 := by
    rw [interval_eq_whole _ a b hab (hz _), ← hinv, ← lift_moment_minus]
    congr 1; funext y; unfold ex; rw [show (-1/2 : ℝ) * y = -y / 2 by ring]
  exact ⟨G1_support (lift g) hG a b hsupp hplus hminus, fun x => (G1_ode (lift g) hG a b x).2⟩

/-! ### Moment-zero parametrisation: smooth, same window

`chi = −G1` is the support-preserving inverse of `D² − 1/4`. It is the composition of the
first-order inverses of `D + 1/2` and `D − 1/2`. If `h` is smooth, supported in `[a, b]`, and both
weighted moments `∫ e^{±u/2} h(u) du` vanish, then `chi` is smooth, supported in `[a, b]`, and
`h = chi'' − chi/4`. -/

open scoped ContDiff

theorem contDiff_ex (c : ℝ) : ContDiff ℝ ∞ (ex c) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id).exp

theorem contDiff_P (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (a : ℝ) : ContDiff ℝ ∞ (P G a) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hasDerivAt_P G hG.continuous a x).differentiableAt, ?_⟩
  rw [show deriv (P G a) = fun x => ex (1/2) x * G x from
    funext fun x => (hasDerivAt_P G hG.continuous a x).deriv]
  exact (contDiff_ex _).mul hG

theorem contDiff_Q (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (b : ℝ) : ContDiff ℝ ∞ (Q G b) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hasDerivAt_Q G hG.continuous b x).differentiableAt, ?_⟩
  rw [show deriv (Q G b) = fun x => ex (-1/2) x * G x from
    funext fun x => (hasDerivAt_Q G hG.continuous b x).deriv]
  exact (contDiff_ex _).mul hG

theorem contDiff_G1 (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (a b : ℝ) : ContDiff ℝ ∞ (G1 G a b) :=
  ((contDiff_ex _).mul (contDiff_P G hG a)).sub ((contDiff_ex _).mul (contDiff_Q G hG b))

/-- A continuous `h` with `tsupport h ⊆ [a, b]` vanishes at `a` and `b` as well. -/
theorem ne_zero_mem_Ioo (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ)
    (hs : tsupport h ⊆ Icc a b) : ∀ y, h y ≠ 0 → y ∈ Ioo a b := by
  have hz : ∀ y, y ∉ Icc a b → h y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h' => hy (hs h'))
  have hcl : IsClosed {x | h x = 0} := isClosed_eq hc continuous_const
  intro y hy
  have hyI : y ∈ Icc a b := by by_contra h'; exact hy (hz y h')
  refine ⟨lt_of_le_of_ne hyI.1 fun he => hy ?_, lt_of_le_of_ne hyI.2 fun he => hy ?_⟩
  · have hsub : Iio a ⊆ {x | h x = 0} := fun x hx => hz x fun hm => absurd hm.1 (not_le.mpr hx)
    have hcl' := hcl.closure_subset_iff.mpr hsub
    rw [closure_Iio] at hcl'
    rw [← he]; exact hcl' self_mem_Iic
  · have hsub : Ioi b ⊆ {x | h x = 0} := fun x hx => hz x fun hm => absurd hm.2 (not_le.mpr hx)
    have hcl' := hcl.closure_subset_iff.mpr hsub
    rw [closure_Ioi] at hcl'
    rw [he]; exact hcl' self_mem_Ici

/-- **Moment-zero parametrisation.** If `h` is smooth with `tsupport h ⊆ [a, b]` and
`∫ e^{−u/2} h(u) du = ∫ e^{u/2} h(u) du = 0`, then `h = chi'' − chi/4` for a smooth `chi` with
`tsupport chi ⊆ [a, b]`, namely `chi = −G1`. -/
theorem moment_zero_parametrization (h : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hh : ContDiff ℝ ∞ h) (hs : tsupport h ⊆ Icc a b)
    (hminus : ∫ u, (Real.exp (-u / 2) : ℂ) * h u = 0)
    (hplus : ∫ u, (Real.exp (u / 2) : ℂ) * h u = 0) :
    ∃ chi : ℝ → ℂ, ContDiff ℝ ∞ chi ∧ tsupport chi ⊆ Icc a b ∧
      ∀ u, h u = deriv (deriv chi) u - (1/4 : ℂ) * chi u := by
  have hc := hh.continuous
  have hsupp := ne_zero_mem_Ioo h hc a b hs
  have hz : ∀ c y, y ∉ Ioo a b → ex c y * h y = 0 := fun c y hy => by
    have : h y = 0 := by by_contra h'; exact hy (hsupp y h')
    rw [this, mul_zero]
  have hp : (∫ y in a..b, ex (1/2) y * h y) = 0 := by
    rw [interval_eq_whole _ a b hab (hz _), ← hplus]
    congr 1; funext y; unfold ex; rw [show (1/2 : ℝ) * y = y / 2 by ring]
  have hm : (∫ y in a..b, ex (-1/2) y * h y) = 0 := by
    rw [interval_eq_whole _ a b hab (hz _), ← hminus]
    congr 1; funext y; unfold ex; rw [show (-1/2 : ℝ) * y = -y / 2 by ring]
  refine ⟨fun x => -G1 h a b x, (contDiff_G1 h hh a b).neg, ?_, fun u => ?_⟩
  · refine closure_minimal (fun x hx => Ioo_subset_Icc_self ?_) isClosed_Icc
    exact G1_support h hc a b hsupp hp hm x fun h0 => hx (by simp [h0])
  · have hd : deriv (fun x => -G1 h a b x) = fun x => -G1' h a b x :=
      funext fun x => (hasDerivAt_G1 h hc a b x).neg.deriv
    rw [hd, show (fun x => -G1' h a b x) = -G1' h a b from rfl, deriv.neg,
      (hasDerivAt_G1' h hc a b u).deriv]
    show h u = -(G1 h a b u / 4 - h u) - (1/4 : ℂ) * -G1 h a b u
    ring

end AEGIS.RHKreinFactorV13

#print axioms AEGIS.RHKreinFactorV13.kreinFactor_support
#print axioms AEGIS.RHKreinFactorV13.kreinFactor_lift_support
#print axioms AEGIS.RHKreinFactorV13.G1_ode
#print axioms AEGIS.RHKreinFactorV13.G1_support
#print axioms AEGIS.RHKreinFactorV13.G1_lift
#print axioms AEGIS.RHKreinFactorV13.contDiff_G1
#print axioms AEGIS.RHKreinFactorV13.moment_zero_parametrization
