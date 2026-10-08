import WeilPairedHadamardFixedLineV1

open Complex

set_option autoImplicit false

noncomputable section

/-- Freeze the multiplicity-aware Hadamard log-derivative surface. -/
example :
    ∃ A : ℂ, ∀ s : ℂ,
      (∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val) →
      _root_.logDeriv LiCriterion.riemannXi s =
        A + ∑' ρ : LiCriterion.NontrivialZero,
          (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            (s / (ρ.val * (s - ρ.val))) :=
  riemannXi_hadamard_logDeriv_with_multiplicity_v1

/-- Freeze the derivative-level consequence of the xi functional equation. -/
example (s : ℂ)
    (hs : LiCriterion.riemannXi s ≠ 0)
    (h1s : LiCriterion.riemannXi (1 - s) ≠ 0) :
    _root_.logDeriv LiCriterion.riemannXi (1 - s) =
      - _root_.logDeriv LiCriterion.riemannXi s :=
  riemannXi_logDeriv_one_sub_v1 s hs h1s

/-- Freeze the pointwise cancellation identity behind the paired kernel. -/
example (s ρ : ℂ) (hρ0 : ρ ≠ 0) (hsρ : s ≠ ρ) (h1sρ : 1 - s ≠ ρ) :
    s / (ρ * (s - ρ)) -
        (1 - s) / (ρ * ((1 - s) - ρ)) =
      1 / (s - ρ) + 1 / (s - (1 - ρ)) :=
  paired_hadamard_partial_fraction_v1 s ρ hρ0 hsρ h1sρ

/-- Freeze the paired fixed-line Hadamard difference before any tsum fusion. -/
example (s : ℂ)
    (hs : ∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val)
    (h1s : ∀ ρ : LiCriterion.NontrivialZero, 1 - s ≠ ρ.val) :
    2 * _root_.logDeriv LiCriterion.riemannXi s =
      (∑' ρ : LiCriterion.NontrivialZero,
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
          (s / (ρ.val * (s - ρ.val)))) -
      (∑' ρ : LiCriterion.NontrivialZero,
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
          ((1 - s) / (ρ.val * ((1 - s) - ρ.val)))) :=
  riemannXi_paired_hadamard_difference_v1 s hs h1s
