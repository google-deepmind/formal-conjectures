import ZeroShellAnalyticSynthesisV1
import Lc.LiCriterion.HadamardSummabilityBridge
import Lc.LiCriterion.XiGrowth
import Hadamard.OrderOne.TailEstimates
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
AEGIS Ω — multiplicity-aware quantitative zero counting v1.

This lane is RH-independent. It reuses the canonical AEGIS nontrivial-zero
carrier and analytic-order multiplicity, while pinning an independently
compiled Jensen/Hadamard provider for the entire Riemann xi function.

The quantitative route is deliberately coarse but sufficient downstream:

* xi and zeta analytic multiplicities agree at every nontrivial zero;
* the provider's order-`≤ 1` Jensen/Hadamard theorem gives cumulative
  multiplicity `O(r^2)` by choosing `ε = 1`;
* every AEGIS height shell `ceil |Im ρ| = n` lies in the centered norm ball
  of radius `n + 1`;
* finitely many radii below the provider threshold are absorbed into one
  explicit finite-prefix constant.

Thus the canonical AEGIS shell multiplicity mass is bounded by
`A * (n + 1)^2` without assuming the Riemann Hypothesis.

ZERO_COUNTING_QUADRATIC_BOUND_V1
RH_INDEPENDENT_ZERO_COUNTING
CRITICAL_LINE_RE_HALF_OPEN
EXPLICIT_FORMULA_OPEN
RH_EQUIVALENCE_OPEN
-/

open Set Filter Topology
open Complex

noncomputable section

/-- A deliberately coarse but sufficient shell-counting certificate. The
quadratic exponent is paired downstream with quartic Mellin decay to recover
the existing quadratic shell-mass certificate. -/
def HasQuadraticShellMultiplicityBoundV1 : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ n : ℕ,
      ZeroHeightShellMultiplicityMassV1 n ≤
        A * (((n : ℝ) + 1) ^ 2)

private theorem li_nontrivial_zero_ne_zero_v1
    (rho : LiCriterion.NontrivialZero) : rho.1 ≠ 0 := by
  intro h
  have hre := rho.2.2.1
  rw [h] at hre
  norm_num at hre

private theorem li_nontrivial_zero_ne_one_v1
    (rho : LiCriterion.NontrivialZero) : rho.1 ≠ 1 := by
  intro h
  have hre := rho.2.2.2
  rw [h] at hre
  norm_num at hre

private theorem li_analyticAt_completedRiemannZeta_v1
    (rho : LiCriterion.NontrivialZero) :
    AnalyticAt ℂ completedRiemannZeta rho.1 := by
  let U : Set ℂ := {0}ᶜ ∩ {1}ᶜ
  have hUopen : IsOpen U := isOpen_compl_singleton.inter isOpen_compl_singleton
  have hrhoU : rho.1 ∈ U := by
    exact ⟨by simpa using li_nontrivial_zero_ne_zero_v1 rho,
      by simpa using li_nontrivial_zero_ne_one_v1 rho⟩
  apply DifferentiableOn.analyticAt (s := U) _ (hUopen.mem_nhds hrhoU)
  intro z hz
  exact (differentiableAt_completedZeta
    (by simpa [U] using hz.1) (by simpa [U] using hz.2)).differentiableWithinAt

private theorem li_analyticOrderAt_zeta_eq_completed_v1
    (rho : LiCriterion.NontrivialZero) :
    analyticOrderAt riemannZeta rho.1 =
      analyticOrderAt completedRiemannZeta rho.1 := by
  let inverseGamma : ℂ → ℂ := fun z => (Complex.Gammaℝ z)⁻¹
  have hinverseAnalytic : AnalyticAt ℂ inverseGamma rho.1 := by
    exact Complex.differentiable_Gammaℝ_inv.analyticAt rho.1
  have hGammaNe : Complex.Gammaℝ rho.1 ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos rho.2.2.1
  have hinverseOrder : analyticOrderAt inverseGamma rho.1 = 0 := by
    exact hinverseAnalytic.analyticOrderAt_eq_zero.mpr (inv_ne_zero hGammaNe)
  have heq :
      riemannZeta =ᶠ[nhds rho.1]
        fun z => completedRiemannZeta z * inverseGamma z := by
    filter_upwards [eventually_ne_nhds (li_nontrivial_zero_ne_zero_v1 rho)] with z hz
    rw [riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]
  calc
    analyticOrderAt riemannZeta rho.1 =
        analyticOrderAt
          (fun z => completedRiemannZeta z * inverseGamma z) rho.1 :=
      analyticOrderAt_congr heq
    _ = analyticOrderAt completedRiemannZeta rho.1 +
        analyticOrderAt inverseGamma rho.1 :=
      analyticOrderAt_mul (li_analyticAt_completedRiemannZeta_v1 rho) hinverseAnalytic
    _ = analyticOrderAt completedRiemannZeta rho.1 := by
      rw [hinverseOrder, add_zero]

private theorem li_xi_eq_half_mul_completed_v1
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    LiCriterion.riemannXi s =
      (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  simpa [LiCriterion.riemannXi, XiZeros.riemannXi] using
    (XiZeros.xi_eq_half_s_sm1_Lambda (s := s) hs0 hs1)

/-- Analytic multiplicity is unchanged by passing from zeta to the provider's
entire xi function at a nontrivial zero. -/
theorem li_xi_zeta_multiplicity_eq_v1
    (rho : LiCriterion.NontrivialZero) :
    analyticOrderNatAt LiCriterion.riemannXi rho.1 =
      analyticOrderNatAt riemannZeta rho.1 := by
  let factor : ℂ → ℂ := fun z => (1 / 2 : ℂ) * z * (z - 1)
  have hfactorAnalytic : AnalyticAt ℂ factor rho.1 := by
    dsimp [factor]
    fun_prop
  have hfactorNe : factor rho.1 ≠ 0 := by
    dsimp [factor]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (li_nontrivial_zero_ne_zero_v1 rho))
      (sub_ne_zero.mpr (li_nontrivial_zero_ne_one_v1 rho))
  have hfactorOrder : analyticOrderAt factor rho.1 = 0 :=
    hfactorAnalytic.analyticOrderAt_eq_zero.mpr hfactorNe
  have heq :
      LiCriterion.riemannXi =ᶠ[nhds rho.1]
        fun z => factor z * completedRiemannZeta z := by
    filter_upwards
      [eventually_ne_nhds (li_nontrivial_zero_ne_zero_v1 rho),
       eventually_ne_nhds (li_nontrivial_zero_ne_one_v1 rho)] with z hz0 hz1
    simpa [factor, mul_assoc] using li_xi_eq_half_mul_completed_v1 hz0 hz1
  have horder :
      analyticOrderAt LiCriterion.riemannXi rho.1 =
        analyticOrderAt riemannZeta rho.1 := by
    calc
      analyticOrderAt LiCriterion.riemannXi rho.1 =
          analyticOrderAt
            (fun z => factor z * completedRiemannZeta z) rho.1 :=
        analyticOrderAt_congr heq
      _ = analyticOrderAt factor rho.1 +
          analyticOrderAt completedRiemannZeta rho.1 :=
        analyticOrderAt_mul hfactorAnalytic
          (li_analyticAt_completedRiemannZeta_v1 rho)
      _ = analyticOrderAt completedRiemannZeta rho.1 := by
        rw [hfactorOrder, zero_add]
      _ = analyticOrderAt riemannZeta rho.1 :=
        (li_analyticOrderAt_zeta_eq_completed_v1 rho).symm
  simp only [analyticOrderNatAt, horder]

/-- Cumulative multiplicity of nontrivial zeta zeros in centered norm balls
is bounded quadratically for all sufficiently large radii. -/
theorem li_zeta_cumulative_quadratic_multiplicity_bound_v1 :
    ∃ R0 C : ℝ, 0 ≤ C ∧
      ∀ r : ℝ, R0 ≤ r →
        (∑ᶠ rho : LiCriterion.NontrivialZero,
          if ‖rho.1‖ ≤ r then
            (analyticOrderNatAt riemannZeta rho.1 : ℝ)
          else 0) ≤ C * r ^ 2 := by
  let Z : Hadamard.ZeroSet LiCriterion.riemannXi := LiCriterion.xiZeroSet
  letI : Countable Z.Zero := by
    dsimp [Z, LiCriterion.xiZeroSet]
    infer_instance
  have hzeros :
      ∀ s : ℂ, LiCriterion.riemannXi s = 0 ↔
        ∃ rho : Z.Zero, s = Z.z rho := by
    intro s
    simpa [Z, LiCriterion.xiZeroSet] using
      (LiCriterion.xi_zeros_are_nontrivial_zeros (s := s))
  have hinj : Function.Injective Z.z := by
    intro rho sigma h
    exact Subtype.ext h
  have hne : ∀ rho : Z.Zero, Z.z rho ≠ 0 := by
    intro rho
    simpa [Z, LiCriterion.xiZeroSet] using rho.ne_zero
  obtain ⟨R0, C, hC, hbound⟩ :=
    Hadamard.OrderOne.sum_multiplicity_zeros_le_rpow_of_order_le
      (f := LiCriterion.riemannXi)
      LiCriterion.xi_entire
      LiCriterion.XiGrowth.riemannXi_hasFiniteOrder
      (lam := (1 : ℝ))
      LiCriterion.XiGrowth.riemannXi_order_le_one
      (by norm_num)
      Z hzeros hinj hne
      (1 : ℝ) (by norm_num)
  refine ⟨R0, C, hC, ?_⟩
  intro r hr
  have hb := hbound r hr
  dsimp [Z, LiCriterion.xiZeroSet] at hb
  have hmult :
      (∑ᶠ rho : LiCriterion.NontrivialZero,
        if ‖rho.1‖ ≤ r then
          (analyticOrderNatAt riemannZeta rho.1 : ℝ)
        else 0) =
      (∑ᶠ rho : LiCriterion.NontrivialZero,
        if ‖rho.1‖ ≤ r then
          (analyticOrderNatAt LiCriterion.riemannXi rho.1 : ℝ)
        else 0) := by
    apply finsum_congr
    intro rho
    split_ifs <;> simp [li_xi_zeta_multiplicity_eq_v1]
  rw [hmult]
  calc
    (∑ᶠ rho : LiCriterion.NontrivialZero,
      if ‖rho.1‖ ≤ r then
        (analyticOrderNatAt LiCriterion.riemannXi rho.1 : ℝ)
      else 0) ≤ C * r ^ ((1 : ℝ) + 1) := hb
    _ = C * r ^ 2 := by
      rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two]

/-- Canonical injection from one AEGIS height shell into the provider's
nontrivial-zero carrier. -/
private def shell_to_li_nontrivial_zero_v1 (n : ℕ) :
    ZeroHeightShellSetV1 n ↪ LiCriterion.NontrivialZero where
  toFun rho := by
    have hstrip :=
      riemann_zeta_nontrivial_zero_critical_strip_v1 rho.1.2.1 rho.1.2.2
    exact ⟨rho.1.1, rho.1.2.1, hstrip.1, hstrip.2⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun rho : LiCriterion.NontrivialZero => rho.1) hab

/-- Every member of the canonical shell `n` lies in the centered norm ball of
radius `n + 1`. -/
private theorem shell_norm_le_succ_v1
    (n : ℕ) (rho : ZeroHeightShellSetV1 n) :
    ‖rho.1.1‖ ≤ (n : ℝ) + 1 := by
  have hstrip :=
    riemann_zeta_nontrivial_zero_critical_strip_v1 rho.1.2.1 rho.1.2.2
  have hre_nonneg : 0 ≤ rho.1.1.re := hstrip.1.le
  have hre_le : rho.1.1.re ≤ 1 := hstrip.2.le
  have hshell : ZeroHeightShellIndexV1 rho.1 = n := rho.2
  have hceil : |rho.1.1.im| ≤ (Nat.ceil |rho.1.1.im| : ℝ) :=
    Nat.le_ceil |rho.1.1.im|
  have him_le : |rho.1.1.im| ≤ (n : ℝ) := by
    rw [show Nat.ceil |rho.1.1.im| = n by
      simpa [ZeroHeightShellIndexV1] using hshell] at hceil
    exact hceil
  calc
    ‖rho.1.1‖ ≤ |rho.1.1.re| + |rho.1.1.im| :=
      Complex.norm_le_abs_re_add_abs_im rho.1.1
    _ = rho.1.1.re + |rho.1.1.im| := by
      rw [abs_of_nonneg hre_nonneg]
    _ ≤ 1 + (n : ℝ) := add_le_add hre_le him_le
    _ = (n : ℝ) + 1 := by ring

/-- Provider nontrivial zeros in a centered norm ball form a finite set. -/
private theorem li_norm_ball_finite_v1 (r : ℝ) :
    {rho : LiCriterion.NontrivialZero | ‖rho.1‖ ≤ r}.Finite := by
  rw [← Set.finite_coe_iff]
  let K : Set ℂ := Metric.closedBall (0 : ℂ) |r| ∩ riemannZetaZeros
  have hK : K.Finite :=
    IsCompact.inter_riemannZetaZeros_finite
      (isCompact_closedBall (0 : ℂ) |r|)
  letI : Fintype K := hK.fintype
  let embed : {rho : LiCriterion.NontrivialZero // ‖rho.1‖ ≤ r} → K := fun rho =>
    ⟨rho.1.1, by
      constructor
      · simp only [Metric.mem_closedBall, dist_zero_right]
        exact rho.2.trans (le_abs_self r)
      · exact mem_riemannZetaZeros.mpr rho.1.2.1⟩
  exact Finite.of_injective embed (by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : K => z.1) hab)

/-- The finite mass of one AEGIS height shell is dominated by the provider's
cumulative multiplicity count in the centered norm ball of radius `n + 1`. -/
private theorem shell_multiplicity_mass_le_li_cumulative_v1 (n : ℕ) :
    ZeroHeightShellMultiplicityMassV1 n ≤
      ∑ᶠ rho : LiCriterion.NontrivialZero,
        if ‖rho.1‖ ≤ (n : ℝ) + 1 then
          (analyticOrderNatAt riemannZeta rho.1 : ℝ)
        else 0 := by
  letI : Fintype (ZeroHeightShellSetV1 n) :=
    (zero_height_shell_finite_v1 n).fintype
  let e := shell_to_li_nontrivial_zero_v1 n
  let f : ZeroHeightShellSetV1 n → ℝ := fun rho =>
    (analyticOrderNatAt riemannZeta rho.1.1 : ℝ)
  let g : LiCriterion.NontrivialZero → ℝ := fun rho =>
    if ‖rho.1‖ ≤ (n : ℝ) + 1 then
      (analyticOrderNatAt riemannZeta rho.1 : ℝ)
    else 0
  have hgfinite : (Function.support g).Finite := by
    apply (li_norm_ball_finite_v1 ((n : ℝ) + 1)).subset
    intro rho hrho
    by_cases hle : ‖rho.1‖ ≤ (n : ℝ) + 1
    · exact hle
    · exfalso
      exact hrho (by simp [g, hle])
  have hf : Summable f := Summable.of_finite
  have hg : Summable g := summable_of_hasFiniteSupport hgfinite
  have hle : (∑' rho, f rho) ≤ ∑' rho, g rho :=
    hf.tsum_le_tsum_of_inj e e.injective
      (fun rho _ => by
        dsimp [g]
        split_ifs <;> positivity)
      (fun rho => by
        have hnorm := shell_norm_le_succ_v1 n rho
        change (analyticOrderNatAt riemannZeta rho.1.1 : ℝ) ≤
          if ‖(e rho).1‖ ≤ (n : ℝ) + 1 then
            (analyticOrderNatAt riemannZeta (e rho).1 : ℝ)
          else 0
        have heval : (e rho).1 = rho.1.1 := by rfl
        have hball : ‖(e rho).1‖ ≤ (n : ℝ) + 1 := by
          simpa [heval] using hnorm
        rw [if_pos hball, heval])
      hg
  rw [tsum_eq_finsum hgfinite] at hle
  simpa [ZeroHeightShellMultiplicityMassV1, f, g] using hle

private theorem zero_height_shell_multiplicity_mass_nonneg_v1 (n : ℕ) :
    0 ≤ ZeroHeightShellMultiplicityMassV1 n := by
  unfold ZeroHeightShellMultiplicityMassV1
  exact tsum_nonneg fun _ => by positivity

/-- Actual multiplicity-safe quantitative shell bound used by the next analytic
synthesis lane. No critical-line hypothesis is used. -/
theorem riemann_zeta_has_quadratic_shell_multiplicity_bound_v1 :
    HasQuadraticShellMultiplicityBoundV1 := by
  obtain ⟨R0, C, hC, hcum⟩ :=
    li_zeta_cumulative_quadratic_multiplicity_bound_v1
  let N : ℕ := Nat.ceil (max R0 1)
  let S : ℝ := (Finset.range N).sum ZeroHeightShellMultiplicityMassV1
  let A : ℝ := max C S
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun k _ =>
      zero_height_shell_multiplicity_mass_nonneg_v1 k
  have hA : 0 ≤ A :=
    hC.trans (le_max_left C S)
  have hCA : C ≤ A := le_max_left C S
  have hSA : S ≤ A := le_max_right C S
  refine ⟨A, hA, ?_⟩
  intro n
  by_cases hn : n < N
  · have hsmall : ZeroHeightShellMultiplicityMassV1 n ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum
        (fun k _ => zero_height_shell_multiplicity_mass_nonneg_v1 k)
        (Finset.mem_range.mpr hn)
    have hr1 : 1 ≤ (((n : ℝ) + 1) ^ 2) := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      nlinarith
    calc
      ZeroHeightShellMultiplicityMassV1 n ≤ S := hsmall
      _ ≤ A := hSA
      _ ≤ A * (((n : ℝ) + 1) ^ 2) :=
        le_mul_of_one_le_right hA hr1
  · have hNn : N ≤ n := Nat.le_of_not_gt hn
    have hR0N : R0 ≤ (N : ℝ) := by
      calc
        R0 ≤ max R0 1 := le_max_left R0 1
        _ ≤ (Nat.ceil (max R0 1) : ℝ) := Nat.le_ceil (max R0 1)
        _ = (N : ℝ) := by rfl
    have hNnR : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hNn
    have hR0r : R0 ≤ (n : ℝ) + 1 := by
      linarith
    have hshell := shell_multiplicity_mass_le_li_cumulative_v1 n
    have hlarge := hcum ((n : ℝ) + 1) hR0r
    have hr2 : 0 ≤ (((n : ℝ) + 1) ^ 2) := sq_nonneg _
    calc
      ZeroHeightShellMultiplicityMassV1 n ≤
          ∑ᶠ rho : LiCriterion.NontrivialZero,
            if ‖rho.1‖ ≤ (n : ℝ) + 1 then
              (analyticOrderNatAt riemannZeta rho.1 : ℝ)
            else 0 := hshell
      _ ≤ C * (((n : ℝ) + 1) ^ 2) := hlarge
      _ ≤ A * (((n : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_right hCA hr2

#check HasQuadraticShellMultiplicityBoundV1
#check li_xi_zeta_multiplicity_eq_v1
#check li_zeta_cumulative_quadratic_multiplicity_bound_v1
#check riemann_zeta_has_quadratic_shell_multiplicity_bound_v1
#print axioms li_xi_zeta_multiplicity_eq_v1
#print axioms li_zeta_cumulative_quadratic_multiplicity_bound_v1
#print axioms riemann_zeta_has_quadratic_shell_multiplicity_bound_v1
