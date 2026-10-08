import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
AEGIS Ω — finite height truncation carrier for nontrivial Riemann-zeta zeros v1.

This lane defines the nontrivial zeta zeros with bounded imaginary height
`|Im(s)| ≤ T` and proves that this set is finite. The proof uses only the
already-established critical-strip geometry `0 < Re(s) < 1`, the pinned
complex norm bound, and Mathlib's pinned theorem that a compact set intersects
the Riemann-zeta zero set in a finite set.

No infinite zero sum or limiting convention is introduced here.

HEIGHT_TRUNCATION_FINITE_ONLY
HEIGHT_LIMIT_EXISTENCE_OPEN
EXPLICIT_FORMULA_OPEN
CRITICAL_LINE_RE_HALF_OPEN
RH_EQUIVALENCE_OPEN
-/

open Complex Set

private theorem zero_nonpos_is_neg_nat_height_local_v1
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

private theorem bernoulli_two_mul_ne_zero_height_local_v1
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

private theorem zeta_neg_odd_ne_zero_height_local_v1 (k : ℕ) :
    riemannZeta (-(((2 * k + 1 : ℕ) : ℂ))) ≠ 0 := by
  rw [riemannZeta_neg_nat_eq_bernoulli (2 * k + 1)]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · have hb : bernoulli (2 * (k + 1)) ≠ 0 :=
        bernoulli_two_mul_ne_zero_height_local_v1 (k + 1) (by omega)
      have hidx : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
      rw [hidx]
      exact_mod_cast hb
  · exact_mod_cast (show (2 * k + 1) + 1 ≠ 0 by omega)

private theorem zeta_neg_nat_zero_iff_trivial_height_local_v1 (n : ℕ) :
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
      · exact ((zeta_neg_odd_ne_zero_height_local_v1 k) hz).elim
  · rintro ⟨k, rfl⟩
    simpa [Nat.cast_mul, Nat.cast_add] using riemannZeta_neg_two_mul_nat_add_one k

private theorem zero_nonpos_is_trivial_height_local_v1
    {s : ℂ} (hz : riemannZeta s = 0) (hre : s.re ≤ 0) :
    ∃ k : ℕ, s = -(2 : ℂ) * (k + 1) := by
  obtain ⟨n, hs⟩ := zero_nonpos_is_neg_nat_height_local_v1 hz hre
  have hzn : riemannZeta (-(n : ℂ)) = 0 := by
    rw [← hs]
    exact hz
  obtain ⟨k, hnk⟩ := (zeta_neg_nat_zero_iff_trivial_height_local_v1 n).mp hzn
  refine ⟨k, ?_⟩
  calc
    s = -(n : ℂ) := hs
    _ = -((2 * (k + 1) : ℕ) : ℂ) := by rw [hnk]
    _ = -(2 : ℂ) * (k + 1) := by push_cast; ring

private theorem nontrivial_zero_critical_strip_height_local_v1
    {s : ℂ} (hz : riemannZeta s = 0)
    (hnontrivial : ¬ ∃ n : ℕ, s = -(2 : ℂ) * (n + 1)) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hpos
    have hre : s.re ≤ 0 := le_of_not_gt hpos
    exact hnontrivial (zero_nonpos_is_trivial_height_local_v1 hz hre)
  · by_contra hlt
    have hge : 1 ≤ s.re := le_of_not_gt hlt
    exact (riemannZeta_ne_zero_of_one_le_re hge) hz

/-- Nontrivial Riemann-zeta zeros with imaginary height at most `T`. -/
def NontrivialZeroHeightSetV1 (T : ℝ) : Set ℂ :=
  {s | riemannZeta s = 0 ∧
       (¬ ∃ n : ℕ, s = -(2 : ℂ) * (n + 1)) ∧
       |s.im| ≤ T}

/-- For every real height bound `T`, the set of nontrivial zeta zeros with
`|Im(s)| ≤ T` is finite.

If such an `s` exists, critical-strip localization gives `0 ≤ Re(s) ≤ 1`.
Together with `|Im(s)| ≤ T`, Mathlib's pinned inequality
`‖s‖ ≤ |Re(s)| + |Im(s)|` places `s` in the closed ball of radius `T + 1`.
The pinned compact-zero theorem then gives finiteness. -/
theorem nontrivial_zero_height_set_finite_v1 (T : ℝ) :
    (NontrivialZeroHeightSetV1 T).Finite := by
  have hfinite :
      (Metric.closedBall (0 : ℂ) (T + 1) ∩ riemannZetaZeros).Finite :=
    IsCompact.inter_riemannZetaZeros_finite (isCompact_closedBall (0 : ℂ) (T + 1))
  refine hfinite.subset ?_
  intro s hs
  change riemannZeta s = 0 ∧
      (¬ ∃ n : ℕ, s = -(2 : ℂ) * (n + 1)) ∧ |s.im| ≤ T at hs
  rcases hs with ⟨hz, hnontrivial, him⟩
  have hstrip := nontrivial_zero_critical_strip_height_local_v1 hz hnontrivial
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

#check NontrivialZeroHeightSetV1
#check nontrivial_zero_height_set_finite_v1
#print axioms nontrivial_zero_height_set_finite_v1
