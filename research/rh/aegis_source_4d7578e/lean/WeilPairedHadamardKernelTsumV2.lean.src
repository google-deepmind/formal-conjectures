import WeilPairedHadamardFixedLineV1
import Mathlib.Tactic

/-!
AEGIS Ω — fused multiplicity-aware paired Hadamard kernel tsum v2.

#519 proves the fixed-line Hadamard identity as the difference of two
multiplicity-weighted tsums.  This module supplies the missing summability
evidence for each weighted genus-one term family, combines them by subtraction,
and then uses the already verified pointwise partial-fraction identity to fuse
that difference into one paired-kernel tsum.

No zero-sum / fixed-line-integral interchange is performed here.  In
particular, the Fubini estimate from the mathematical #490 proof remains a
separate obligation.  No arithmetic sign inequality or RH claim is asserted.
-/

open Complex
open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-- A single multiplicity-weighted genus-one Hadamard term family is genuinely
summable away from the nontrivial zeros.  The proof expands multiplicity into
the provider's sigma carrier, applies its summable log-derivative theorem, and
then regroups the finite multiplicity fibres. -/
theorem riemannXi_weighted_hadamard_term_summable_v2
    (s : ℂ)
    (hs : ∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val) :
    Summable (fun ρ : LiCriterion.NontrivialZero =>
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        (s / (ρ.val * (s - ρ.val)))) := by
  classical
  have hgenus :=
    LiCriterion.xi_weighted_genus_one_of_hadamard_order_one
      LiCriterion.XiGrowth.riemannXi_hasFiniteOrder
      LiCriterion.XiGrowth.riemannXi_order_le_one
  have hsigma_genus :=
    LiCriterion.summable_inv_norm_sq_zeros_with_multiplicity_of_weighted_genus
      hgenus
  have hsigma_log :
      Summable (fun i : LiCriterion.XiZeroWithMultiplicity =>
        _root_.logDeriv
          (fun w : ℂ => Hadamard.weierstrass_E 1 (w / i.1.val)) s) := by
    exact
      Hadamard.OrderOne.summable_logDeriv_weierstrass_E_one_div_of_summable_inv_norm_sq
        (z := fun i : LiCriterion.XiZeroWithMultiplicity => i.1.val)
        (fun i => i.1.ne_zero) hsigma_genus s (fun i => hs i.1)
  have hsigma_term :
      Summable (fun i : LiCriterion.XiZeroWithMultiplicity =>
        s / (i.1.val * (s - i.1.val))) := by
    refine hsigma_log.congr ?_
    intro i
    exact
      Hadamard.OrderOne.logDeriv_weierstrass_E_one_div
        (a := i.1.val) (x := s) i.1.ne_zero (hs i.1)
  have hweighted :
      HasSum
        (fun ρ : LiCriterion.NontrivialZero =>
          ∑' _k : Fin (analyticOrderNatAt LiCriterion.riemannXi ρ.val),
            s / (ρ.val * (s - ρ.val)))
        (∑' i : LiCriterion.XiZeroWithMultiplicity,
          s / (i.1.val * (s - i.1.val))) := by
    simpa [LiCriterion.XiZeroWithMultiplicity] using
      hsigma_term.hasSum.sigma
        (fun ρ =>
          hasSum_fintype
            (fun _k : Fin (analyticOrderNatAt LiCriterion.riemannXi ρ.val) =>
              s / (ρ.val * (s - ρ.val))))
  refine hweighted.summable.congr ?_
  intro ρ
  calc
    (∑' _k : Fin (analyticOrderNatAt LiCriterion.riemannXi ρ.val),
        s / (ρ.val * (s - ρ.val)))
        =
      ∑ _k : Fin (analyticOrderNatAt LiCriterion.riemannXi ρ.val),
        s / (ρ.val * (s - ρ.val)) := by
          simp
    _ =
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        (s / (ρ.val * (s - ρ.val))) := by
          simp [Finset.card_univ, nsmul_eq_mul]

/-- The multiplicity-weighted paired partial-fraction kernel is summable.
This is the load-bearing legality required before fusing the two totalized
tsums from #519. -/
theorem riemannXi_paired_hadamard_kernel_summable_v2
    (s : ℂ)
    (hs : ∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val)
    (h1s : ∀ ρ : LiCriterion.NontrivialZero, 1 - s ≠ ρ.val) :
    Summable (fun ρ : LiCriterion.NontrivialZero =>
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        (1 / (s - ρ.val) + 1 / (s - (1 - ρ.val)))) := by
  have hleft := riemannXi_weighted_hadamard_term_summable_v2 s hs
  have hright :=
    riemannXi_weighted_hadamard_term_summable_v2 (1 - s) h1s
  refine (hleft.sub hright).congr ?_
  intro ρ
  calc
    (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
          (s / (ρ.val * (s - ρ.val))) -
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
          ((1 - s) / (ρ.val * ((1 - s) - ρ.val)))
        =
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        (s / (ρ.val * (s - ρ.val)) -
          (1 - s) / (ρ.val * ((1 - s) - ρ.val))) := by
            ring
    _ =
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        (1 / (s - ρ.val) + 1 / (s - (1 - ρ.val))) := by
          rw [paired_hadamard_partial_fraction_v1
            s ρ.val ρ.ne_zero (hs ρ) (h1s ρ)]

/-- Fuse #519's difference of two individually summable Hadamard tsums into
one multiplicity-weighted paired-kernel tsum. -/
theorem riemannXi_paired_hadamard_kernel_tsum_v2
    (s : ℂ)
    (hs : ∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val)
    (h1s : ∀ ρ : LiCriterion.NontrivialZero, 1 - s ≠ ρ.val) :
    2 * _root_.logDeriv LiCriterion.riemannXi s =
      ∑' ρ : LiCriterion.NontrivialZero,
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
          (1 / (s - ρ.val) + 1 / (s - (1 - ρ.val))) := by
  have hleft := riemannXi_weighted_hadamard_term_summable_v2 s hs
  have hright :=
    riemannXi_weighted_hadamard_term_summable_v2 (1 - s) h1s
  have hdiff := riemannXi_paired_hadamard_difference_v1 s hs h1s
  rw [← hleft.tsum_sub hright] at hdiff
  calc
    2 * _root_.logDeriv LiCriterion.riemannXi s =
        ∑' ρ : LiCriterion.NontrivialZero,
          ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
              (s / (ρ.val * (s - ρ.val))) -
            (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
              ((1 - s) / (ρ.val * ((1 - s) - ρ.val)))) := hdiff
    _ =
        ∑' ρ : LiCriterion.NontrivialZero,
          (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            (1 / (s - ρ.val) + 1 / (s - (1 - ρ.val))) := by
      apply tsum_congr
      intro ρ
      calc
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
              (s / (ρ.val * (s - ρ.val))) -
            (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
              ((1 - s) / (ρ.val * ((1 - s) - ρ.val)))
            =
          (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            (s / (ρ.val * (s - ρ.val)) -
              (1 - s) / (ρ.val * ((1 - s) - ρ.val))) := by
                ring
        _ =
          (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            (1 / (s - ρ.val) + 1 / (s - (1 - ρ.val))) := by
              rw [paired_hadamard_partial_fraction_v1
                s ρ.val ρ.ne_zero (hs ρ) (h1s ρ)]

end

#print axioms riemannXi_weighted_hadamard_term_summable_v2
#print axioms riemannXi_paired_hadamard_kernel_summable_v2
#print axioms riemannXi_paired_hadamard_kernel_tsum_v2
