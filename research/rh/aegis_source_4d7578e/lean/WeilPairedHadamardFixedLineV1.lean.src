import WeilFixedLineExplicitFormulaContractV2
import Lc.LiCriterion.HadamardBridge
import Lc.LiCriterion.XiGrowth
import Lc.LiCriterion.HadamardSummabilityBridge
import Hadamard.OrderOne.LogDerivMultiplicity
import Mathlib.Tactic

/-!
AEGIS Ω — paired Hadamard fixed-line zero kernel v1.

This module composes the existing multiplicity-aware genus-one provider with
`riemannXi`'s functional equation on the same Lean 4.33.1 / Mathlib pin used by
#488/#490/#493/#507/#511.

It deliberately stops at the difference of two individually controlled
Hadamard log-derivative sums.  It does not fuse that difference into one
paired-kernel `tsum`, does not prove the normalized explicit formula, and does
not prove the arithmetic sign inequality or RH.
-/

open Complex Filter Topology
open scoped BigOperators

set_option autoImplicit false

noncomputable section

private theorem riemannXi_ne_zero_of_avoids_nontrivial_zeros_v1
    (s : ℂ) (hs : ∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val) :
    LiCriterion.riemannXi s ≠ 0 := by
  intro hzero
  obtain ⟨ρ, hρ⟩ := (LiCriterion.xi_zeros_are_nontrivial_zeros (s := s)).mp hzero
  exact hs ρ hρ

/-- Multiplicity-aware Hadamard log derivative of the completed zeta function.
The constant `A` is the linear exponential coefficient in the genus-one
factorization. -/
theorem riemannXi_hadamard_logDeriv_with_multiplicity_v1 :
    ∃ A : ℂ, ∀ s : ℂ,
      (∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val) →
      _root_.logDeriv LiCriterion.riemannXi s =
        A + ∑' ρ : LiCriterion.NontrivialZero,
          (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            (s / (ρ.val * (s - ρ.val))) := by
  obtain ⟨A, B, hfac⟩ :=
    LiCriterion.xi_hadamard_factorization_with_multiplicity
      LiCriterion.XiGrowth.riemannXi_hasFiniteOrder
      LiCriterion.XiGrowth.riemannXi_order_le_one
  refine ⟨A, ?_⟩
  intro s hs
  let P : ℂ → ℂ := LiCriterion.xiMultiplicityE1Prod
  have hsum :=
    LiCriterion.xi_weighted_genus_one_of_hadamard_order_one
      LiCriterion.XiGrowth.riemannXi_hasFiniteOrder
      LiCriterion.XiGrowth.riemannXi_order_le_one
  have hP_explicit :
      P = fun w : ℂ =>
        ∏' j : Hadamard.OrderOne.WithMultiplicity
            LiCriterion.NontrivialZero
            (fun ρ => analyticOrderNatAt LiCriterion.riemannXi ρ.val),
          Hadamard.weierstrass_E 1 (w / j.1.val) := by
    funext w
    calc
      P w = LiCriterion.xiMultiplicityE1Prod w := rfl
      _ = LiCriterion.xiE1ProdWithMultiplicity w :=
        LiCriterion.xiMultiplicityE1Prod_eq_xiE1ProdWithMultiplicity w
      _ = (∏' j : Hadamard.OrderOne.WithMultiplicity
              LiCriterion.NontrivialZero
              (fun ρ => analyticOrderNatAt LiCriterion.riemannXi ρ.val),
            Hadamard.weierstrass_E 1 (w / j.1.val)) := rfl
  have hlogP :
      _root_.logDeriv P s =
        ∑' ρ : LiCriterion.NontrivialZero,
          (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            (s / (ρ.val * (s - ρ.val))) := by
    rw [hP_explicit]
    exact
      Hadamard.OrderOne.logDeriv_tprod_weierstrass_E_one_eq_tsum_of_summable_mul_inv_norm_sq
        (z := fun ρ : LiCriterion.NontrivialZero => ρ.val)
        (m := fun ρ : LiCriterion.NontrivialZero =>
          analyticOrderNatAt LiCriterion.riemannXi ρ.val)
        (fun ρ => ρ.ne_zero) hsum s hs
  have hxi_ne : LiCriterion.riemannXi s ≠ 0 :=
    riemannXi_ne_zero_of_avoids_nontrivial_zeros_v1 s hs
  have hP_ne : P s ≠ 0 := by
    intro hP
    apply hxi_ne
    calc
      LiCriterion.riemannXi s = Complex.exp (A * s + B) * P s := by
        simpa [P] using hfac s
      _ = 0 := by rw [hP, mul_zero]
  have hP_eq :
      P = fun w : ℂ => LiCriterion.riemannXi w / Complex.exp (A * w + B) := by
    funext w
    apply (eq_div_iff (Complex.exp_ne_zero (A * w + B))).2
    rw [hfac w]
    ring
  have hP_diff : Differentiable ℂ P := by
    rw [hP_eq]
    exact LiCriterion.xi_entire.div (by fun_prop)
      (fun w => Complex.exp_ne_zero (A * w + B))
  have hexp_log :
      _root_.logDeriv (fun w : ℂ => Complex.exp (A * w + B)) s = A := by
    rw [_root_.logDeriv_apply, deriv_cexp (by fun_prop)]
    simp
  have hfun :
      LiCriterion.riemannXi =
        fun w : ℂ => Complex.exp (A * w + B) * P w := by
    funext w
    simpa [P] using hfac w
  have hmul :
      _root_.logDeriv LiCriterion.riemannXi s =
        _root_.logDeriv (fun w : ℂ => Complex.exp (A * w + B)) s +
          _root_.logDeriv P s := by
    rw [hfun]
    exact _root_.logDeriv_mul s
      (Complex.exp_ne_zero (A * s + B)) hP_ne
      (by fun_prop) hP_diff.differentiableAt
  calc
    _root_.logDeriv LiCriterion.riemannXi s
        = _root_.logDeriv (fun w : ℂ => Complex.exp (A * w + B)) s +
            _root_.logDeriv P s := hmul
    _ = A + ∑' ρ : LiCriterion.NontrivialZero,
          (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            (s / (ρ.val * (s - ρ.val))) := by
          rw [hexp_log, hlogP]

/-- The functional equation `ξ(s)=ξ(1-s)` makes the logarithmic derivative
antisymmetric under `s ↦ 1-s`.  Nonvanishing hypotheses keep the statement on
the intended off-zero surface. -/
theorem riemannXi_logDeriv_one_sub_v1 (s : ℂ)
    (hs : LiCriterion.riemannXi s ≠ 0)
    (h1s : LiCriterion.riemannXi (1 - s) ≠ 0) :
    _root_.logDeriv LiCriterion.riemannXi (1 - s) =
      - _root_.logDeriv LiCriterion.riemannXi s := by
  have hcomp := _root_.logDeriv_comp
    (f := LiCriterion.riemannXi)
    (g := fun z : ℂ => 1 - z)
    (x := s)
    LiCriterion.xi_entire.differentiableAt
    (by fun_prop)
  have hfun :
      (LiCriterion.riemannXi ∘ fun z : ℂ => 1 - z) =
        LiCriterion.riemannXi := by
    funext z
    exact (LiCriterion.xi_functional_equation z).symm
  rw [hfun] at hcomp
  simp at hcomp
  calc
    _root_.logDeriv LiCriterion.riemannXi (1 - s)
        = -(- _root_.logDeriv LiCriterion.riemannXi (1 - s)) := by ring
    _ = - _root_.logDeriv LiCriterion.riemannXi s := by rw [hcomp]

/-- Algebraic cancellation of the genus-one correction terms when the two
Hadamard logarithmic derivatives at `s` and `1-s` are subtracted. -/
theorem paired_hadamard_partial_fraction_v1
    (s ρ : ℂ) (hρ0 : ρ ≠ 0) (hsρ : s ≠ ρ) (h1sρ : 1 - s ≠ ρ) :
    s / (ρ * (s - ρ)) -
        (1 - s) / (ρ * ((1 - s) - ρ)) =
      1 / (s - ρ) + 1 / (s - (1 - ρ)) := by
  have hs_pair : s ≠ 1 - ρ := by
    intro h
    apply h1sρ
    rw [h]
    ring
  field_simp [hρ0, sub_ne_zero.mpr hsρ, sub_ne_zero.mpr h1sρ,
    sub_ne_zero.mpr hs_pair]
  ring

/-- Paired fixed-line Hadamard difference.  The linear exponential coefficient
cancels after the `ξ(s)=ξ(1-s)` log-derivative antisymmetry.  This theorem
intentionally leaves the two absolutely controlled `tsum`s separate. -/
theorem riemannXi_paired_hadamard_difference_v1 (s : ℂ)
    (hs : ∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val)
    (h1s : ∀ ρ : LiCriterion.NontrivialZero, 1 - s ≠ ρ.val) :
    2 * _root_.logDeriv LiCriterion.riemannXi s =
      (∑' ρ : LiCriterion.NontrivialZero,
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
          (s / (ρ.val * (s - ρ.val)))) -
      (∑' ρ : LiCriterion.NontrivialZero,
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
          ((1 - s) / (ρ.val * ((1 - s) - ρ.val)))) := by
  obtain ⟨A, hA⟩ := riemannXi_hadamard_logDeriv_with_multiplicity_v1
  have hsA := hA s hs
  have h1sA := hA (1 - s) h1s
  have hs_ne := riemannXi_ne_zero_of_avoids_nontrivial_zeros_v1 s hs
  have h1s_ne := riemannXi_ne_zero_of_avoids_nontrivial_zeros_v1 (1 - s) h1s
  have hsym := riemannXi_logDeriv_one_sub_v1 s hs_ne h1s_ne
  rw [hsym] at h1sA
  linear_combination hsA - h1sA

end

#print axioms riemannXi_hadamard_logDeriv_with_multiplicity_v1
#print axioms riemannXi_logDeriv_one_sub_v1
#print axioms paired_hadamard_partial_fraction_v1
#print axioms riemannXi_paired_hadamard_difference_v1
