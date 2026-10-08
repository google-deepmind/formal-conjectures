import WeilFixedLineCompletedGammaV10
import WeilFixedLineZeroSideV10
import ZeroCountingBoundV1
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-!
AEGIS Ω — pinned-compatible xi logarithmic-derivative decomposition V10.

On Re(s) > 1 this module derives, on the exact Mathlib pin used by the RH
lane,

  xi'/xi(s)
    = 1/s + 1/(s-1)
      - (log pi)/2 + (1/2) psi(s/2)
      + zeta'/zeta(s).

No newer Mathlib convenience theorem is imported: the Gamma_R logarithmic
derivative is rebuilt from the pinned const-cpow derivative, Gamma chain rule,
and the pinned definition of digamma.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex
open scoped Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilXiLogDerivDecompositionV10

/-- Logarithmic derivative of Deligne's real Gamma factor on the positive
half-plane, proved against the pinned Mathlib API. -/
theorem logDeriv_GammaR_v10 (s : ℂ) (hs : 0 < s.re) :
    _root_.logDeriv Complex.Gammaℝ s =
      -(((Real.log Real.pi : ℝ) : ℂ) / 2) +
        (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
  let p : ℂ → ℂ := fun z => (Real.pi : ℂ) ^ (-z / 2)
  let g : ℂ → ℂ := fun z => Complex.Gamma (z / 2)

  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

  have hpDer :
      HasDerivAt p
        ((Real.pi : ℂ) ^ (-s / 2) *
          Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    have hlin :
        HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) s := by
      simpa using (hasDerivAt_id s).neg.div_const 2
    simpa [p] using hlin.const_cpow (Or.inl hpi)

  have hpne : p s ≠ 0 := by
    dsimp [p]
    rw [Complex.cpow_def_of_ne_zero hpi]
    exact Complex.exp_ne_zero _

  have hs2 : 0 < (s / 2).re := by
    simpa using (div_pos hs (by norm_num : (0 : ℝ) < 2))

  have hGammaNe : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hs2

  have hGammaDiff : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma (s / 2) (by
      intro m h
      have hre := congrArg Complex.re h
      simp at hre
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)

  have hhalf :
      DifferentiableAt ℂ (fun z : ℂ => z / 2) s := by
    fun_prop

  have hgDiff : DifferentiableAt ℂ g s := by
    dsimp [g]
    exact hGammaDiff.comp s hhalf

  have hgNe : g s ≠ 0 := by
    simpa [g] using hGammaNe

  have hpLog :
      _root_.logDeriv p s =
        -(((Real.log Real.pi : ℝ) : ℂ) / 2) := by
    rw [_root_.logDeriv_apply, hpDer.deriv]
    have hlog :
        Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
      rw [← Complex.ofReal_log Real.pi_pos.le]
    rw [hlog]
    dsimp [p] at hpne ⊢
    field_simp [hpne]

  have hgLog :
      _root_.logDeriv g s =
        (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
    have hcomp :=
      _root_.logDeriv_comp
        (f := Complex.Gamma)
        (g := fun z : ℂ => z / 2)
        hGammaDiff hhalf
    change _root_.logDeriv g s =
      (1 / 2 : ℂ) * Complex.digamma (s / 2)
    dsimp [g]
    rw [show (fun z : ℂ => Complex.Gamma (z / 2)) =
        Complex.Gamma ∘ (fun z : ℂ => z / 2) by rfl,
      hcomp, ← Complex.digamma_def]
    simp
    ring

  change
    _root_.logDeriv (fun z : ℂ =>
      (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s =
      _
  rw [_root_.logDeriv_mul s hpne hgNe
    hpDer.differentiableAt hgDiff, hpLog, hgLog]

/-- Local factorization of xi by the four nonconstant factors on Re(s)>1. -/
private theorem xi_factorization_eventually_v10
    (s : ℂ) (hs : 1 < s.re) :
    LiCriterion.riemannXi =ᶠ[𝓝 s]
      (fun z : ℂ =>
        (1 / 2 : ℂ) *
          (((z * (z - 1)) * Complex.Gammaℝ z) * riemannZeta z)) := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := by
    exact Complex.continuous_re.isOpen_preimage (Ioi (1 : ℝ)) isOpen_Ioi
  have hsMem : s ∈ {z : ℂ | 1 < z.re} := hs
  filter_upwards [hopen.mem_nhds hsMem] with z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hz
  have hGamma : Complex.Gammaℝ z ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hz)
  have hxi :
      LiCriterion.riemannXi z =
        (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta z := by
    simpa [LiCriterion.riemannXi, XiZeros.riemannXi] using
      (XiZeros.xi_eq_half_s_sm1_Lambda (s := z) hz0 hz1)
  have hzetaDef :=
    riemannZeta_def_of_ne_zero hz0
  have hcompleted :
      completedRiemannZeta z =
        Complex.Gammaℝ z * riemannZeta z := by
    rw [hzetaDef]
    field_simp [hGamma]
  rw [hxi, hcompleted]
  ring

/-- Pointwise xi logarithmic-derivative decomposition on Re(s)>1. -/
theorem xi_logDeriv_decomposition_v10
    (s : ℂ) (hs : 1 < s.re) :
    _root_.logDeriv LiCriterion.riemannXi s =
      1 / s + 1 / (s - 1) +
        (-(((Real.log Real.pi : ℝ) : ℂ) / 2) +
          (1 / 2 : ℂ) * Complex.digamma (s / 2)) +
        deriv riemannZeta s / riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hGamma : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs)
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs

  have hGammaDiff : DifferentiableAt ℂ Complex.Gammaℝ s := by
    have hGdef : Complex.Gammaℝ =
        fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
      funext z
      exact Complex.Gammaℝ_def z
    rw [hGdef]
    apply DifferentiableAt.mul
    · have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hpi0)
    · have hs2 : 0 < (s / 2).re := by
        simpa using (div_pos (lt_trans zero_lt_one hs)
          (by norm_num : (0 : ℝ) < 2))
      exact
        (Complex.differentiableAt_Gamma (s / 2) (by
          intro m h
          have hre := congrArg Complex.re h
          simp at hre
          have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith)).comp s (by fun_prop)

  have hzetaDiff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1

  let A : ℂ → ℂ := fun z => z
  let B : ℂ → ℂ := fun z => z - 1
  let C : ℂ → ℂ := Complex.Gammaℝ
  let D : ℂ → ℂ := riemannZeta

  have hAne : A s ≠ 0 := hs0
  have hBne : B s ≠ 0 := sub_ne_zero.mpr hs1
  have hCne : C s ≠ 0 := hGamma
  have hDne : D s ≠ 0 := hzeta

  have hAd : DifferentiableAt ℂ A s := by
    dsimp [A]
    fun_prop
  have hBd : DifferentiableAt ℂ B s := by
    dsimp [B]
    fun_prop
  have hCd : DifferentiableAt ℂ C s := by
    simpa [C] using hGammaDiff
  have hDd : DifferentiableAt ℂ D s := by
    simpa [D] using hzetaDiff

  have hAB :
      _root_.logDeriv (fun z => A z * B z) s =
        _root_.logDeriv A s + _root_.logDeriv B s :=
    _root_.logDeriv_mul s hAne hBne hAd hBd
  have hABC :
      _root_.logDeriv (fun z => (A z * B z) * C z) s =
        _root_.logDeriv (fun z => A z * B z) s +
          _root_.logDeriv C s :=
    _root_.logDeriv_mul s
      (mul_ne_zero hAne hBne) hCne (hAd.mul hBd) hCd
  have hABCD :
      _root_.logDeriv (fun z => ((A z * B z) * C z) * D z) s =
        _root_.logDeriv (fun z => (A z * B z) * C z) s +
          _root_.logDeriv D s :=
    _root_.logDeriv_mul s
      (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne
      ((hAd.mul hBd).mul hCd) hDd

  have hxiEq :=
    (_root_.logDeriv_congr_nhds
      (xi_factorization_eventually_v10 s hs)).eq_of_nhds

  have hconst :
      _root_.logDeriv
        (fun z : ℂ =>
          (1 / 2 : ℂ) * (((z * (z - 1)) * Complex.Gammaℝ z) *
            riemannZeta z)) s =
      _root_.logDeriv
        (fun z : ℂ => (((z * (z - 1)) * Complex.Gammaℝ z) *
          riemannZeta z)) s := by
    exact _root_.logDeriv_const_mul s (1 / 2 : ℂ) (by norm_num)

  have hAlog : _root_.logDeriv A s = 1 / s := by
    simpa [A] using (_root_.logDeriv_id' s)
  have hBlog : _root_.logDeriv B s = 1 / (s - 1) := by
    dsimp [B]
    simp [_root_.logDeriv_apply, hs1]
  have hClog :
      _root_.logDeriv C s =
        -(((Real.log Real.pi : ℝ) : ℂ) / 2) +
          (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
    simpa [C] using logDeriv_GammaR_v10 s (lt_trans zero_lt_one hs)
  have hDlog :
      _root_.logDeriv D s =
        deriv riemannZeta s / riemannZeta s := by
    rfl

  calc
    _root_.logDeriv LiCriterion.riemannXi s
      = _root_.logDeriv
          (fun z : ℂ =>
            (1 / 2 : ℂ) * (((z * (z - 1)) * Complex.Gammaℝ z) *
              riemannZeta z)) s := hxiEq
    _ = _root_.logDeriv
          (fun z : ℂ => (((z * (z - 1)) * Complex.Gammaℝ z) *
            riemannZeta z)) s := hconst
    _ =
      _root_.logDeriv
        (fun z => ((A z * B z) * C z) * D z) s := by rfl
    _ =
      (_root_.logDeriv A s + _root_.logDeriv B s) +
        _root_.logDeriv C s + _root_.logDeriv D s := by
          rw [hABCD, hABC, hAB]
    _ = _ := by
      rw [hAlog, hBlog, hClog, hDlog]

/-- Fixed-line form consumed by the whole explicit-formula assembly. -/
theorem xi_logDeriv_fixed_line_decomposition_v10
    (c t : ℝ) (hc : 1 < c) :
    _root_.logDeriv LiCriterion.riemannXi
        ((c : ℂ) + (t : ℂ) * I) =
      1 / ((c : ℂ) + (t : ℂ) * I) +
      1 / (((c : ℂ) + (t : ℂ) * I) - 1) +
      AEGIS.WeilFixedLineCompletedGammaV10.WeilCompletedGammaFactorV10 c t +
      deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
        riemannZeta ((c : ℂ) + (t : ℂ) * I) := by
  have hs : 1 < (((c : ℂ) + (t : ℂ) * I)).re := by
    simpa using hc
  simpa [AEGIS.WeilFixedLineCompletedGammaV10.WeilCompletedGammaFactorV10]
    using xi_logDeriv_decomposition_v10
      ((c : ℂ) + (t : ℂ) * I) hs

end AEGIS.WeilXiLogDerivDecompositionV10

#print axioms AEGIS.WeilXiLogDerivDecompositionV10.logDeriv_GammaR_v10
#print axioms AEGIS.WeilXiLogDerivDecompositionV10.xi_logDeriv_decomposition_v10
#print axioms AEGIS.WeilXiLogDerivDecompositionV10.xi_logDeriv_fixed_line_decomposition_v10
