import WeilPairedHadamardKernelTsumV2

open Complex
open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-- Freeze summability of one multiplicity-weighted Hadamard term family. -/
example (s : ℂ)
    (hs : ∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val) :
    Summable (fun ρ : LiCriterion.NontrivialZero =>
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        (s / (ρ.val * (s - ρ.val)))) :=
  riemannXi_weighted_hadamard_term_summable_v2 s hs

/-- Freeze absolute control of the single paired partial-fraction kernel. -/
example (s : ℂ)
    (hs : ∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val)
    (h1s : ∀ ρ : LiCriterion.NontrivialZero, 1 - s ≠ ρ.val) :
    Summable (fun ρ : LiCriterion.NontrivialZero =>
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        (1 / (s - ρ.val) + 1 / (s - (1 - ρ.val)))) :=
  riemannXi_paired_hadamard_kernel_summable_v2 s hs h1s

/-- Freeze fusion of the difference of two weighted tsums into one paired-kernel tsum. -/
example (s : ℂ)
    (hs : ∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val)
    (h1s : ∀ ρ : LiCriterion.NontrivialZero, 1 - s ≠ ρ.val) :
    2 * _root_.logDeriv LiCriterion.riemannXi s =
      ∑' ρ : LiCriterion.NontrivialZero,
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
          (1 / (s - ρ.val) + 1 / (s - (1 - ρ.val))) :=
  riemannXi_paired_hadamard_kernel_tsum_v2 s hs h1s
