import RHHatBudgetV13
import RHCellCapsV13

/-!
AEGIS Ω — the hat-kernel Weil diagonal with Coxeter caps, V13.

`RHHatBudgetV13` bounds `Re C(u)` by `E` on `(0, t₁]`, by `0.71E` on `(t₁, t₂]` and by `E/2`
beyond.  The N-cell caps of `RHCellCapsV13` give `Re C(u) ≤ K_N·E` once `2r < N·u`, with
`K_N ≥ cos(π/(N+1))` (the spectral bound of the path `A_N`).  Here the region `(0, 2r]` is
cut at `s₇ ≤ s₆ ≤ s₅ ≤ s₄ ≤ s₃ ≤ s₂ ≤ 2r` with caps

  `1 | 93/100 | 91/100 | 87/100 | 81/100 | 71/100 | 1/2`.

Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHatCoxBudgetV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilWidthArchBudgetV26
open AEGIS.WeilWidthArchIntegralV27
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHMomentPiecesV13
open AEGIS.RHMomentGainV13
open AEGIS.RHMomentIdentityV13
open AEGIS.RHHalfCapV13
open AEGIS.RHThreeCellV13
open AEGIS.RHThresholdClassV13
open AEGIS.RHHatPosDefV13
open AEGIS.RHHatKernelV13
open AEGIS.RHHatBudgetV13
open AEGIS.RHCellCapsV13

/-- The archimedean part is bounded by the tail plus the hat integrand on `(0, 2r]`. -/
theorem arch_le_hatIntegral (g : WeilCompactSmoothGV1) (r a lam σ h : ℝ) (n : ℕ)
    (v : ℕ → ℝ) (hr0 : 0 < r) (hh : 0 ≤ h) (hσ : 0 ≤ σ)
    (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * (-cothTail (2 * r)) + ∫ u in Ioc 0 (2 * r), hatIntegrand g lam σ h n v u := by
  set E := energy g.1 with hE
  have hE0 : 0 ≤ E := energy_nonnegative g.1
  have h2r : 0 ≤ 2 * r := by linarith
  rw [archimedean_real_eq_log_integral_v27, split_at g (2 * r) h2r, tail_eq g r a hr0 hw]
  have hMi : IntegrableOn (momentLog g) (Ioc 0 (2 * r)) :=
    (moment_log_integrableOn g).mono_set (fun u hu => hu.1)
  have hCKi : IntegrableOn (fun u => cRe g u * hatK h n v u) (Ioc 0 (2 * r)) :=
    ((cRe_continuous g).mul (hatK_continuous h n v)).integrableOn_Ioc
  have hHi := hatIntegrand_integrableOn g lam σ h n v 0 (2 * r) le_rfl
  have hdecomp : (∫ u in Ioc 0 (2 * r), widthArchLogIntegrandV26 g u) =
      (∫ u in Ioc 0 (2 * r), hatIntegrand g lam σ h n v u) +
        lam * (∫ u in Ioc 0 (2 * r), momentLog g u) -
        σ * ∫ u in Ioc 0 (2 * r), cRe g u * hatK h n v u := by
    have hA : IntegrableOn (fun u => hatIntegrand g lam σ h n v u + lam * momentLog g u)
        (Ioc 0 (2 * r)) := hHi.add (hMi.const_mul lam)
    have hB : IntegrableOn (fun u => σ * (cRe g u * hatK h n v u)) (Ioc 0 (2 * r)) :=
      hCKi.const_mul σ
    have hL : IntegrableOn (fun u => lam * momentLog g u) (Ioc 0 (2 * r)) := hMi.const_mul lam
    calc (∫ u in Ioc 0 (2 * r), widthArchLogIntegrandV26 g u)
        = ∫ u in Ioc 0 (2 * r), ((hatIntegrand g lam σ h n v u + lam * momentLog g u) -
            σ * (cRe g u * hatK h n v u)) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro u _
          simp only [hatIntegrand]
          ring
      _ = (∫ u in Ioc 0 (2 * r), (hatIntegrand g lam σ h n v u + lam * momentLog g u)) -
            ∫ u in Ioc 0 (2 * r), σ * (cRe g u * hatK h n v u) := integral_sub hA hB
      _ = _ := by
          rw [integral_add hHi hL, integral_const_mul, integral_const_mul]
  have hmom : (∫ u in Ioc 0 (2 * r), momentLog g u) = 0 := by
    rw [← integral_zero_beyond (momentLog g) (2 * r) h2r (moment_log_integrableOn g)]
    · exact moment_log_identity g hm
    · intro u hu
      unfold momentLog
      rw [autocorrelation_zero_of_halfWidth g r a u hw hu]
      simp
  have hpd : 0 ≤ ∫ u in Ioc 0 (2 * r), cRe g u * hatK h n v u := by
    have hz : ∀ u, 2 * r < u → cRe g u * hatK h n v u = 0 := by
      intro u hu; simp [cRe_zero g r a u hw hu]
    have hIoi : IntegrableOn (fun u => cRe g u * hatK h n v u) (Ioi 0) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi h2r]
      apply IntegrableOn.union hCKi
      exact integrableOn_zero.congr_fun (fun u hu => (hz u hu).symm) measurableSet_Ioi
    rw [← integral_zero_beyond (fun u => cRe g u * hatK h n v u) (2 * r) h2r hIoi hz]
    exact hat_posdef_packet g h hh n v
  rw [hdecomp, hmom]
  have hσpd := mul_nonneg hσ hpd
  nlinarith

/-- The gain of one capped region `(lo, hi]`, per unit energy. -/
def regionGain (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ) (lo hi c : ℝ) : ℝ :=
  -(1 - c) * (cothTail lo - cothTail hi) +
    c * ((hi - lo) / 2 + (hi ^ 2 - lo ^ 2) / 16 -
      4 * lam * (Real.sinh (hi / 2) - Real.sinh (lo / 2)) +
      σ * ∫ u in Ioc lo hi, hatK h n v u)

/-- The gain of the uncapped first region `(0, b]`, per unit energy. -/
def firstGain (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ) (b : ℝ) : ℝ :=
  b / 2 + b ^ 2 / 16 - 4 * lam * Real.sinh (b / 2) + σ * ∫ u in Ioc 0 b, hatK h n v u

/-- **Region bound.**  A cap `Re C ≤ c·E` on `(lo, hi]` bounds the hat integrand there. -/
theorem region_bound (g : WeilCompactSmoothGV1) (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ)
    (lo hi c : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) (hc0 : 0 ≤ c)
    (hQ : ∀ u ∈ Ioc lo hi, 0 ≤ kernelQ lam σ h n v u)
    (hcap : ∀ u ∈ Ioc lo hi, cRe g u ≤ c * energy g.1) :
    (∫ u in Ioc lo hi, hatIntegrand g lam σ h n v u) ≤
      energy g.1 * regionGain lam σ h n v lo hi c := by
  set E := energy g.1 with hE
  have hkc : Continuous (hatK h n v) := hatK_continuous h n v
  have hmaj : IntegrableOn (fun u => -(1 - c) * E * (1 / Real.sinh u) +
      c * E * (1 / 2 + u / 8 - 2 * lam * Real.cosh (u / 2) + σ * hatK h n v u)) (Ioc lo hi) := by
    have hs := (integrableOn_inv_sinh_Ioc lo hi hlo).const_mul (-(1 - c) * E)
    have hrest : IntegrableOn (fun u : ℝ => c * E * (1 / 2 + u / 8 - 2 * lam * Real.cosh (u / 2) +
        σ * hatK h n v u)) (Ioc lo hi) :=
      ((continuous_const.mul ((continuous_const.add (continuous_id.div_const 8)).sub
        (continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2)))
        |>.add (continuous_const.mul hkc)))).integrableOn_Ioc
    exact hs.add hrest
  have hint : (∫ u in Ioc lo hi, hatIntegrand g lam σ h n v u) ≤
      ∫ u in Ioc lo hi, (-(1 - c) * E * (1 / Real.sinh u) +
        c * E * (1 / 2 + u / 8 - 2 * lam * Real.cosh (u / 2) + σ * hatK h n v u)) := by
    apply setIntegral_mono_on (hatIntegrand_integrableOn g lam σ h n v lo hi hlo.le) hmaj
      measurableSet_Ioc
    intro u hu
    exact hatIntegrand_le g lam σ h n v u c (lt_of_lt_of_le hlo hu.1.le) (le_trans hu.2 hhi) hc0
      (hQ u hu) (hcap u hu)
  rw [region_integral g lam σ h n v lo hi c hlo hlohi] at hint
  unfold regionGain
  nlinarith [hint]

/-- The first region `(0, b]` with the trivial cap `Re C ≤ E`. -/
theorem first_bound (g : WeilCompactSmoothGV1) (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ)
    (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hQ : ∀ u ∈ Ioc 0 b, 0 ≤ kernelQ lam σ h n v u) :
    (∫ u in Ioc 0 b, hatIntegrand g lam σ h n v u) ≤
      energy g.1 * firstGain lam σ h n v b := by
  have hkc : Continuous (hatK h n v) := hatK_continuous h n v
  unfold firstGain
  rw [← region_integral_zero g lam σ h n v b hb.le]
  apply setIntegral_mono_on (hatIntegrand_integrableOn g lam σ h n v 0 b le_rfl) _
    measurableSet_Ioc
  · intro u hu
    exact hatIntegrand_le_one g lam σ h n v u hu.1 (le_trans hu.2 hb1) (hQ u hu)
  · exact ((continuous_const.mul ((continuous_const.add (continuous_id.div_const 8)).sub
      (continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2)))
      |>.add (continuous_const.mul hkc)))).integrableOn_Ioc

/-- Split `∫_{(a,c]}` at `b`. -/
theorem split_hat (g : WeilCompactSmoothGV1) (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ)
    (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ u in Ioc a c, hatIntegrand g lam σ h n v u) =
      (∫ u in Ioc a b, hatIntegrand g lam σ h n v u) +
        ∫ u in Ioc b c, hatIntegrand g lam σ h n v u := by
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc, setIntegral_union
    (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (hatIntegrand_integrableOn g lam σ h n v a b ha)
    (hatIntegrand_integrableOn g lam σ h n v b c (le_trans ha hab))]

/-- A cell cap `‖C(u)‖ ≤ K·E` for `2r < N·u` gives `Re C ≤ K·E` on `(s, hi]` once `2r ≤ N·s`. -/
theorem cap_of_cell (g : WeilCompactSmoothGV1) (r a s hi K N : ℝ) (hs : 0 < s)
    (hN : 2 * r ≤ N * s) (hNpos : 0 < N)
    (hcell : ∀ u, 2 * r < N * u → 0 < u → ‖logCorrelationV25 g u‖ ≤ K * energy g.1) :
    ∀ u ∈ Ioc s hi, cRe g u ≤ K * energy g.1 := by
  intro u hu
  have hu0 : 0 < u := lt_trans hs hu.1
  have h1 : 2 * r < N * u := lt_of_le_of_lt hN (mul_lt_mul_of_pos_left hu.1 hNpos)
  unfold cRe
  exact le_trans (Complex.re_le_norm _) (hcell u h1 hu0)

/-- The Coxeter-capped hat gain. -/
def hatCoxGain (r lam σ h s7 s6 s5 s4 s3 s2 : ℝ) (n : ℕ) (v : ℕ → ℝ) : ℝ :=
  diagonalKappaV21 - cothTail (2 * r)
    + firstGain lam σ h n v s7
    + regionGain lam σ h n v s7 s6 (93 / 100)
    + regionGain lam σ h n v s6 s5 (91 / 100)
    + regionGain lam σ h n v s5 s4 (87 / 100)
    + regionGain lam σ h n v s4 s3 (81 / 100)
    + regionGain lam σ h n v s3 s2 (71 / 100)
    + regionGain lam σ h n v s2 (2 * r) (1 / 2)

/-- **Coxeter hat diagonal.**  Below `log 2`, `Re RHS(A) ≤ hatCoxGain · E`. -/
theorem hatcox_diagonal (g : WeilCompactSmoothGV1) (r a lam σ h s7 s6 s5 s4 s3 s2 : ℝ)
    (n : ℕ) (v : ℕ → ℝ) (hr0 : 0 < r) (hr1 : 2 * r ≤ 1) (hlog : 2 * r < Real.log 2)
    (hh : 0 ≤ h) (hσ : 0 ≤ σ) (hs7 : 0 < s7)
    (h7 : 2 * r ≤ 7 * s7) (h6 : 2 * r ≤ 6 * s6) (h5 : 2 * r ≤ 5 * s5) (h4 : 2 * r ≤ 4 * s4)
    (h3 : 2 * r ≤ 3 * s3) (h2 : r ≤ s2)
    (h76 : s7 ≤ s6) (h65 : s6 ≤ s5) (h54 : s5 ≤ s4) (h43 : s4 ≤ s3) (h32 : s3 ≤ s2)
    (h2r : s2 ≤ 2 * r)
    (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g)
    (hQ : ∀ u ∈ Ioc 0 (2 * r), 0 ≤ kernelQ lam σ h n v u) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤
      hatCoxGain r lam σ h s7 s6 s5 s4 s3 s2 n v * energy g.1 := by
  set E := energy g.1 with hE
  have hE0 : 0 ≤ E := energy_nonnegative g.1
  have hp := prime_sum_zero_of_halfWidth g r a hw hlog
  have harch := arch_le_hatIntegral g r a lam σ h n v hr0 hh hσ hw hm
  have hQs : ∀ lo hi : ℝ, 0 ≤ lo → hi ≤ 2 * r → ∀ u ∈ Ioc lo hi, 0 ≤ kernelQ lam σ h n v u :=
    fun lo hi hlo hhi u hu => hQ u ⟨lt_of_le_of_lt hlo hu.1, le_trans hu.2 hhi⟩
  have hs6 : 0 < s6 := lt_of_lt_of_le hs7 h76
  have hs5 : 0 < s5 := lt_of_lt_of_le hs6 h65
  have hs4 : 0 < s4 := lt_of_lt_of_le hs5 h54
  have hs3 : 0 < s3 := lt_of_lt_of_le hs4 h43
  have hs2 : 0 < s2 := lt_of_lt_of_le hs3 h32
  -- splits
  rw [split_hat g lam σ h n v 0 s7 (2 * r) le_rfl hs7.le (by linarith),
    split_hat g lam σ h n v s7 s6 (2 * r) hs7.le h76 (by linarith),
    split_hat g lam σ h n v s6 s5 (2 * r) hs6.le h65 (by linarith),
    split_hat g lam σ h n v s5 s4 (2 * r) hs5.le h54 (by linarith),
    split_hat g lam σ h n v s4 s3 (2 * r) hs4.le h43 (by linarith),
    split_hat g lam σ h n v s3 s2 (2 * r) hs3.le h32 h2r] at harch
  have b0 := first_bound g lam σ h n v s7 hs7 (by linarith) (hQs 0 s7 le_rfl (by linarith))
  have b7 := region_bound g lam σ h n v s7 s6 (93 / 100) hs7 h76 (by linarith) (by norm_num)
    (hQs s7 s6 hs7.le (by linarith))
    (cap_of_cell g r a s7 s6 (93 / 100) 7 hs7 h7 (by norm_num)
      (fun u hu hu0 => cell7_logCorrelation g r a u hw hu hu0))
  have b6 := region_bound g lam σ h n v s6 s5 (91 / 100) hs6 h65 (by linarith) (by norm_num)
    (hQs s6 s5 hs6.le (by linarith))
    (cap_of_cell g r a s6 s5 (91 / 100) 6 hs6 h6 (by norm_num)
      (fun u hu hu0 => cell6_logCorrelation g r a u hw hu hu0))
  have b5 := region_bound g lam σ h n v s5 s4 (87 / 100) hs5 h54 (by linarith) (by norm_num)
    (hQs s5 s4 hs5.le (by linarith))
    (cap_of_cell g r a s5 s4 (87 / 100) 5 hs5 h5 (by norm_num)
      (fun u hu hu0 => cell5_logCorrelation g r a u hw hu hu0))
  have b4 := region_bound g lam σ h n v s4 s3 (81 / 100) hs4 h43 (by linarith) (by norm_num)
    (hQs s4 s3 hs4.le (by linarith))
    (cap_of_cell g r a s4 s3 (81 / 100) 4 hs4 h4 (by norm_num)
      (fun u hu hu0 => cell4_logCorrelation g r a u hw hu hu0))
  have b3 := region_bound g lam σ h n v s3 s2 (71 / 100) hs3 h32 (by linarith) (by norm_num)
    (hQs s3 s2 hs3.le h2r)
    (cap_of_cell g r a s3 s2 (71 / 100) 3 hs3 h3 (by norm_num)
      (fun u hu hu0 => three_cell_logCorrelation g r a u hw hu hu0))
  have b2 := region_bound g lam σ h n v s2 (2 * r) (1 / 2) hs2 h2r hr1 (by norm_num)
    (hQs s2 (2 * r) hs2.le le_rfl)
    (by
      intro u hu
      have hru : r < u := lt_of_le_of_lt h2 hu.1
      have := half_cap_logCorrelation g r a u hw hru
      unfold cRe
      linarith [Complex.re_le_norm (logCorrelationV25 g u)])
  change (B g g).re ≤ _
  rw [actual_diagonal_rhs_decomposition g hp]
  unfold hatCoxGain
  nlinarith [energy_nonnegative g.1]

end AEGIS.RHHatCoxBudgetV13

#print axioms AEGIS.RHHatCoxBudgetV13.arch_le_hatIntegral
#print axioms AEGIS.RHHatCoxBudgetV13.region_bound
#print axioms AEGIS.RHHatCoxBudgetV13.hatcox_diagonal
