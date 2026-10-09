import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
AEGIS Ω — multiplicity-safe finite height sum for nontrivial Riemann-zeta zeros v1.

This lane builds only a finite, height-bounded zero carrier and a finite
multiplicity-weighted Mellin sum over that carrier. Every multiplicity is the
natural analytic order of `riemannZeta` at the corresponding zero, with a
proof that the order is finite and strictly positive.

No infinite zero sum, convergence claim, limiting convention, explicit
formula, critical-line assertion, or RH implication is introduced here.

FINITE_HEIGHT_SUM_ONLY
HEIGHT_LIMIT_EXISTENCE_OPEN
ZERO_SUM_CONVERGENCE_OPEN
EXPLICIT_FORMULA_OPEN
CRITICAL_LINE_RE_HALF_OPEN
RH_EQUIVALENCE_OPEN
-/

open Set Filter Topology
open Complex

noncomputable section

private theorem zero_nonpos_is_neg_nat_height_sum_local_v1
    {s : ℂ} (hz : riemannZeta s = 0) (hre : s.re ≤ 0) :
    ∃ n : ℕ, s = -n := by
  by_contra hneg
  have hnotnat : ∀ n : ℕ, s ≠ -n := by
    intro n hsn
    exact hneg ⟨n, hsn⟩
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) (by simpa using hre)
  have hzero_reflected : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_one_sub hnotnat hs1, hz, mul_zero]
  have hge : 1 ≤ (1 - s).re := by
    simpa [sub_eq_add_neg] using
      (le_add_of_nonneg_right (neg_nonneg.mpr hre) : (1 : ℝ) ≤ 1 + (-s.re))
  exact (riemannZeta_ne_zero_of_one_le_re hge) hzero_reflected

private theorem bernoulli_two_mul_ne_zero_height_sum_local_v1
    (k : ℕ) (hk : k ≠ 0) : bernoulli (2 * k) ≠ 0 := by
  intro hB
  have hzeta0 : riemannZeta (2 * (k : ℂ)) = 0 := by
    rw [riemannZeta_two_mul_nat hk, hB]
    simp
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hge : (1 : ℝ) ≤ (2 * (k : ℂ)).re := by
    norm_num
    linarith
  exact (riemannZeta_ne_zero_of_one_le_re hge) hzeta0

private theorem zeta_neg_odd_ne_zero_height_sum_local_v1 (k : ℕ) :
    riemannZeta (-(((2 * k + 1 : ℕ) : ℂ))) ≠ 0 := by
  rw [riemannZeta_neg_nat_eq_bernoulli (2 * k + 1)]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · have hb : bernoulli (2 * (k + 1)) ≠ 0 :=
        bernoulli_two_mul_ne_zero_height_sum_local_v1 (k + 1) (by omega)
      have hidx : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
      rw [hidx]
      exact_mod_cast hb
  · exact_mod_cast (show (2 * k + 1) + 1 ≠ 0 by omega)

private theorem zeta_neg_nat_zero_iff_trivial_height_sum_local_v1 (n : ℕ) :
    riemannZeta (-(n : ℂ)) = 0 ↔ ∃ k : ℕ, n = 2 * (k + 1) := by
  constructor
  · intro hz
    by_cases hn : n = 0
    · subst n
      norm_num [riemannZeta_zero] at hz
    · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · have hk : k ≠ 0 := by
          intro hk
          subst k
          simp at hn
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        exact ⟨j, rfl⟩
      · exact ((zeta_neg_odd_ne_zero_height_sum_local_v1 k) hz).elim
  · rintro ⟨k, rfl⟩
    simpa [Nat.cast_mul, Nat.cast_add] using riemannZeta_neg_two_mul_nat_add_one k

private theorem zero_nonpos_is_trivial_height_sum_local_v1
    {s : ℂ} (hz : riemannZeta s = 0) (hre : s.re ≤ 0) :
    ∃ k : ℕ, s = -(2 : ℂ) * (k + 1) := by
  obtain ⟨n, hs⟩ := zero_nonpos_is_neg_nat_height_sum_local_v1 hz hre
  have hzn : riemannZeta (-(n : ℂ)) = 0 := by
    rw [← hs]
    exact hz
  obtain ⟨k, hnk⟩ := (zeta_neg_nat_zero_iff_trivial_height_sum_local_v1 n).mp hzn
  refine ⟨k, ?_⟩
  calc
    s = -(n : ℂ) := hs
    _ = -((2 * (k + 1) : ℕ) : ℂ) := by rw [hnk]
    _ = -(2 : ℂ) * (k + 1) := by push_cast; ring

private theorem nontrivial_zero_critical_strip_height_sum_local_v1
    {s : ℂ} (hz : riemannZeta s = 0)
    (hnontrivial : ¬ ∃ n : ℕ, s = -(2 : ℂ) * (n + 1)) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hpos
    have hre : s.re ≤ 0 := le_of_not_gt hpos
    exact hnontrivial (zero_nonpos_is_trivial_height_sum_local_v1 hz hre)
  · by_contra hlt
    have hge : 1 ≤ s.re := le_of_not_gt hlt
    exact (riemannZeta_ne_zero_of_one_le_re hge) hz

/-- Nontrivial Riemann-zeta zeros with imaginary height at most `T`. -/
def NontrivialZeroHeightSetV1 (T : ℝ) : Set ℂ :=
  {s | riemannZeta s = 0 ∧
       (¬ ∃ n : ℕ, s = -(2 : ℂ) * (n + 1)) ∧
       |s.im| ≤ T}

private theorem nontrivial_zero_height_set_finite_sum_local_v1 (T : ℝ) :
    (NontrivialZeroHeightSetV1 T).Finite := by
  have hfinite :
      (Metric.closedBall (0 : ℂ) (T + 1) ∩ riemannZetaZeros).Finite :=
    IsCompact.inter_riemannZetaZeros_finite (isCompact_closedBall (0 : ℂ) (T + 1))
  refine hfinite.subset ?_
  intro s hs
  change riemannZeta s = 0 ∧
      (¬ ∃ n : ℕ, s = -(2 : ℂ) * (n + 1)) ∧ |s.im| ≤ T at hs
  rcases hs with ⟨hz, hnontrivial, him⟩
  have hstrip := nontrivial_zero_critical_strip_height_sum_local_v1 hz hnontrivial
  have hre_nonneg : 0 ≤ s.re := hstrip.1.le
  have hre_le : s.re ≤ 1 := hstrip.2.le
  constructor
  · simp only [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = s.re + |s.im| := by rw [abs_of_nonneg hre_nonneg]
      _ ≤ 1 + T := add_le_add hre_le him
      _ = T + 1 := by ring
  · exact mem_riemannZetaZeros.mpr hz

/-- Canonical finite carrier obtained from the verified finite height set. -/
noncomputable def NontrivialZeroHeightFinsetV1 (T : ℝ) : Finset ℂ :=
  (nontrivial_zero_height_set_finite_sum_local_v1 T).toFinset

private theorem mem_nontrivial_zero_height_finset_v1 {T : ℝ} {s : ℂ} :
    s ∈ NontrivialZeroHeightFinsetV1 T ↔ s ∈ NontrivialZeroHeightSetV1 T := by
  simp [NontrivialZeroHeightFinsetV1]

/-- Natural analytic-order multiplicity used for each finite-height zero. -/
def HeightZeroMultiplicityV1 (s : ℂ) : ℕ :=
  analyticOrderNatAt riemannZeta s

private theorem riemannZeta_order_ne_top_at_height_zero_v1
    {T : ℝ} {s : ℂ} (hs : s ∈ NontrivialZeroHeightFinsetV1 T) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have hsSet : s ∈ NontrivialZeroHeightSetV1 T :=
    mem_nontrivial_zero_height_finset_v1.mp hs
  rcases hsSet with ⟨hz, hnontrivial, _him⟩
  have hstrip := nontrivial_zero_critical_strip_height_sum_local_v1 hz hnontrivial
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hstrip
  intro htop
  have hlocal : riemannZeta =ᶠ[𝓝 s] (fun _ : ℂ => 0) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz'
    exact hz'
  have hsU : s ∈ ({1}ᶜ : Set ℂ) := by
    simpa using hs1
  have heq : Set.EqOn riemannZeta (fun _ : ℂ => 0) ({1}ᶜ : Set ℂ) :=
    analyticOn_riemannZeta.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      hsU hlocal
  have hzero : riemannZeta (0 : ℂ) = 0 := by
    simpa using heq (by simp : (0 : ℂ) ∈ ({1}ᶜ : Set ℂ))
  rw [riemannZeta_zero] at hzero
  norm_num at hzero

/-- Every member of the finite height carrier receives a strictly positive
analytic-order multiplicity. -/
theorem height_zero_multiplicity_pos_v1
    {T : ℝ} {s : ℂ} (hs : s ∈ NontrivialZeroHeightFinsetV1 T) :
    0 < HeightZeroMultiplicityV1 s := by
  have hsSet : s ∈ NontrivialZeroHeightSetV1 T :=
    mem_nontrivial_zero_height_finset_v1.mp hs
  rcases hsSet with ⟨hz, hnontrivial, _him⟩
  have hstrip := nontrivial_zero_critical_strip_height_sum_local_v1 hz hnontrivial
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hstrip
  have hsU : s ∈ ({1}ᶜ : Set ℂ) := by
    simpa using hs1
  have hAn : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s hsU
  have horder_ne0 : analyticOrderAt riemannZeta s ≠ 0 :=
    hAn.analyticOrderAt_ne_zero.mpr hz
  have horder_netop : analyticOrderAt riemannZeta s ≠ ⊤ :=
    riemannZeta_order_ne_top_at_height_zero_v1 hs
  apply Nat.pos_of_ne_zero
  intro hnat
  have hnat' : analyticOrderNatAt riemannZeta s = 0 := by
    simpa [HeightZeroMultiplicityV1] using hnat
  apply horder_ne0
  calc
    analyticOrderAt riemannZeta s =
        (analyticOrderNatAt riemannZeta s : ℕ∞) :=
      (Nat.cast_analyticOrderNatAt horder_netop).symm
    _ = 0 := by simp [hnat']

/-- Casting the finite-height multiplicity back to `ℕ∞` recovers the analytic
order exactly; no multiplicity information is discarded. -/
theorem height_zero_multiplicity_cast_eq_order_v1
    {T : ℝ} {s : ℂ} (hs : s ∈ NontrivialZeroHeightFinsetV1 T) :
    (HeightZeroMultiplicityV1 s : ℕ∞) = analyticOrderAt riemannZeta s := by
  unfold HeightZeroMultiplicityV1
  exact Nat.cast_analyticOrderNatAt (riemannZeta_order_ne_top_at_height_zero_v1 hs)

/-- Pointwise multiplicity-weighted Mellin contribution at one finite-height zero. -/
def WeilZeroHeightSummandV1 (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  (HeightZeroMultiplicityV1 s : ℂ) * mellin f s

/-- Finite multiplicity-weighted Mellin sum over nontrivial zeros of height at
most `T`. This is deliberately a `Finset.sum`, not an infinite sum or limit. -/
noncomputable def WeilZeroHeightTruncatedSumV1 (f : ℝ → ℂ) (T : ℝ) : ℂ :=
  (NontrivialZeroHeightFinsetV1 T).sum (fun s => WeilZeroHeightSummandV1 f s)

#check NontrivialZeroHeightFinsetV1
#check HeightZeroMultiplicityV1
#check height_zero_multiplicity_pos_v1
#check height_zero_multiplicity_cast_eq_order_v1
#check WeilZeroHeightSummandV1
#check WeilZeroHeightTruncatedSumV1
#print axioms height_zero_multiplicity_pos_v1
#print axioms height_zero_multiplicity_cast_eq_order_v1
