/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Erdős 265 standalone Lean4Web proof
Proof by Kenta Kitamura, from the modular development at
https://github.com/KitaKen1/erdos-265-lean/tree/16db9f29ad68a861552f74b8c2fe2148433c3e80/lean.
The root/limsup interface below is an additional adaptation.
-/


/-!
# Erdős Problem 265: statement

This file fixes the indexing ambiguity in the informal statement by requiring
`2 ≤ a 0`.  The two reciprocal series are required to be summable as real
series and to have rational sums.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos265

/-- An admissible sequence for Erdős Problem 265. -/
def IsRationalPairSequence (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧
    2 ≤ a 0 ∧
    Summable (fun n : ℕ ↦ (1 : ℝ) / (a n : ℝ)) ∧
    Summable (fun n : ℕ ↦ (1 : ℝ) / ((a n : ℝ) - 1)) ∧
    (∃ q : ℚ, ∑' n : ℕ, (1 : ℝ) / (a n : ℝ) = (q : ℝ)) ∧
    (∃ q : ℚ, ∑' n : ℕ, (1 : ℝ) / ((a n : ℝ) - 1) = (q : ℝ))

/-- The robust, infinitely-often formulation of
`limsup a_n^(1 / 2^n) > 1`. -/
def GrowthExceedsOne (a : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 1 < c ∧ ∃ᶠ n in atTop, c ^ (2 ^ n) ≤ (a n : ℝ)

/-- The logarithmic form of the claimed critical-base-two conclusion. -/
noncomputable def CriticalLogRatio (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.log (a n : ℝ) / (2 : ℝ) ^ n

/-- The target theorem from the human proof.  This declaration is a proposition,
not an axiom: the proof is assembled in later files. -/
def CriticalBaseTwoConclusion (a : ℕ → ℕ) : Prop :=
  Tendsto (CriticalLogRatio a) atTop (𝓝 0)

end Erdos265

/-!
# Critical logarithmic growth excludes base-two spikes

This file is independent of the arithmetic-series argument.  It proves that
the logarithmic conclusion claimed in the report really answers the robust
`limsup > 1` formulation of Erdős 265.
-/

open Filter Topology

namespace Erdos265

theorem two_le_of_isRationalPairSequence {a : ℕ → ℕ}
    (ha : IsRationalPairSequence a) (n : ℕ) : 2 ≤ a n :=
  le_trans ha.2.1 (ha.1.monotone (Nat.zero_le n))

theorem positive_of_isRationalPairSequence {a : ℕ → ℕ}
    (ha : IsRationalPairSequence a) (n : ℕ) : 0 < (a n : ℝ) := by
  exact_mod_cast (show 0 < a n from lt_of_lt_of_le (by omega) (two_le_of_isRationalPairSequence ha n))

/-- If `log a_n / 2^n → 0`, then no fixed `c > 1` can satisfy
`c^(2^n) ≤ a_n` infinitely often. -/
theorem not_growthExceedsOne_of_tendsto_logRatio {a : ℕ → ℕ}
    (ha_pos : ∀ n, 0 < (a n : ℝ))
    (hlim : Tendsto (CriticalLogRatio a) atTop (𝓝 0)) :
    ¬ GrowthExceedsOne a := by
  rintro ⟨c, hc, hfrequent⟩
  have hc_pos : 0 < c := lt_trans zero_lt_one hc
  have hlogc : 0 < Real.log c := Real.log_pos hc
  have heventual : ∀ᶠ n in atTop, CriticalLogRatio a n < Real.log c :=
    (tendsto_order.1 hlim).2 _ hlogc
  obtain ⟨n, hcn, hnsmall⟩ := (hfrequent.and_eventually heventual).exists
  have hpow_pos : 0 < c ^ (2 ^ n) := pow_pos hc_pos _
  have hlog_le : Real.log (c ^ (2 ^ n)) ≤ Real.log (a n : ℝ) :=
    (Real.log_le_log_iff hpow_pos (ha_pos n)).2 hcn
  have hscaled : Real.log c * (2 : ℝ) ^ n ≤ Real.log (a n : ℝ) := by
    simpa [Real.log_pow, Nat.cast_pow, mul_comm] using hlog_le
  have hden_pos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hratio : Real.log c ≤ CriticalLogRatio a n := by
    rw [CriticalLogRatio, le_div_iff₀ hden_pos]
    exact hscaled
  exact (not_lt_of_ge hratio) hnsmall

/-- The report's logarithmic conclusion gives the negative answer to the
critical-base-two decision question. -/
theorem criticalBaseTwoConclusion_implies_negative_answer {a : ℕ → ℕ}
    (ha : IsRationalPairSequence a)
    (h : CriticalBaseTwoConclusion a) :
    ¬ GrowthExceedsOne a :=
  not_growthExceedsOne_of_tendsto_logRatio
    (positive_of_isRationalPairSequence ha) h

end Erdos265

/-!
# Tails of the two reciprocal series

This file first establishes the analytic tail identities.  The denominator
arithmetic needed for the rational lower bounds is developed below these
general lemmas.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos265

/-- The tail beginning at index `n`, written with a fixed `ℕ` index type. -/
noncomputable def SeriesTail (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, f (k + n)

theorem summable_seriesTail {f : ℕ → ℝ} (hf : Summable f) (n : ℕ) :
    Summable (fun k : ℕ ↦ f (k + n)) :=
  (summable_nat_add_iff n).2 hf

/-- Remove the first term from a summable tail. -/
theorem seriesTail_eq_add_succ {f : ℕ → ℝ} (hf : Summable f) (n : ℕ) :
    SeriesTail f n = f n + SeriesTail f (n + 1) := by
  rw [SeriesTail, SeriesTail]
  rw [(summable_seriesTail hf n).tsum_eq_zero_add]
  congr 1
  · simp
  · apply tsum_congr
    intro k
    congr 1
    omega

/-- Tails of any real series converge to zero. -/
theorem seriesTail_tendsto_zero (f : ℕ → ℝ) :
    Tendsto (SeriesTail f) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ ∑' k : ℕ, f (k + n)) atTop (𝓝 0)
  exact tendsto_sum_nat_add f

/-- The reciprocal term `1/a_n`. -/
noncomputable def ReciprocalTerm (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  1 / (a n : ℝ)

/-- The shifted reciprocal term `1/(a_n-1)`. -/
noncomputable def ShiftedReciprocalTerm (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  1 / ((a n : ℝ) - 1)

/-- `T_n = ∑_{k≥n} 1/a_k`. -/
noncomputable def ReciprocalTail (a : ℕ → ℕ) : ℕ → ℝ :=
  SeriesTail (ReciprocalTerm a)

/-- `V_n = ∑_{k≥n} 1/(a_k-1)`. -/
noncomputable def ShiftedReciprocalTail (a : ℕ → ℕ) : ℕ → ℝ :=
  SeriesTail (ShiftedReciprocalTerm a)

/-- The positive termwise difference of the two reciprocal series. -/
noncomputable def DifferenceTerm (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  1 / ((a n : ℝ) * ((a n : ℝ) - 1))

/-- `D_n = ∑_{k≥n} 1/(a_k(a_k-1))`. -/
noncomputable def DifferenceTail (a : ℕ → ℕ) : ℕ → ℝ :=
  SeriesTail (DifferenceTerm a)

theorem shifted_sub_reciprocal_eq_difference
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    ShiftedReciprocalTerm a n - ReciprocalTerm a n = DifferenceTerm a n := by
  have ha0 : (0 : ℝ) < a n := by exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  have ha1 : (0 : ℝ) < (a n : ℝ) - 1 := by
    have hacast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
    linarith
  rw [ShiftedReciprocalTerm, ReciprocalTerm, DifferenceTerm]
  field_simp
  ring

/-- The difference of the two tails is the tail of their termwise
difference. -/
theorem shiftedTail_sub_reciprocalTail_eq_differenceTail
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a)) (n : ℕ) :
    ShiftedReciprocalTail a n - ReciprocalTail a n = DifferenceTail a n := by
  change
    (∑' k : ℕ, ShiftedReciprocalTerm a (k + n)) -
        (∑' k : ℕ, ReciprocalTerm a (k + n)) =
      ∑' k : ℕ, DifferenceTerm a (k + n)
  rw [← (summable_seriesTail hv n).tsum_sub (summable_seriesTail hu n)]
  apply tsum_congr
  intro k
  exact shifted_sub_reciprocal_eq_difference ha (k + n)

theorem reciprocalTerm_nonneg
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    0 ≤ ReciprocalTerm a n := by
  have hcast : (0 : ℝ) < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  rw [ReciprocalTerm]
  exact (one_div_pos.mpr hcast).le

theorem differenceTerm_pos
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    0 < DifferenceTerm a n := by
  have hacast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
  have ha0 : (0 : ℝ) < (a n : ℝ) := by linarith
  have ha1 : (0 : ℝ) < (a n : ℝ) - 1 := by linarith
  rw [DifferenceTerm]
  exact one_div_pos.mpr (mul_pos ha0 ha1)

theorem summable_differenceTerm
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a)) :
    Summable (DifferenceTerm a) := by
  apply (hv.sub hu).congr
  intro n
  exact shifted_sub_reciprocal_eq_difference ha n

theorem differenceTail_eq_add_succ
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a)) (n : ℕ) :
    DifferenceTail a n = DifferenceTerm a n + DifferenceTail a (n + 1) :=
  seriesTail_eq_add_succ (summable_differenceTerm ha hu hv) n

theorem differenceTail_nonneg
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    0 ≤ DifferenceTail a n := by
  rw [DifferenceTail, SeriesTail]
  exact tsum_nonneg fun k ↦ (differenceTerm_pos ha (k + n)).le

theorem differenceTail_pos
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a)) (n : ℕ) :
    0 < DifferenceTail a n := by
  rw [differenceTail_eq_add_succ ha hu hv n]
  exact add_pos_of_pos_of_nonneg (differenceTerm_pos ha n)
    (differenceTail_nonneg ha (n + 1))

theorem reciprocalTail_nonneg
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    0 ≤ ReciprocalTail a n := by
  rw [ReciprocalTail, SeriesTail]
  exact tsum_nonneg fun k ↦ reciprocalTerm_nonneg ha (k + n)

/-- Since `a` is increasing, every factor `1/(a_k-1)` in `D_n` is at
most `1/(a_n-1)`. -/
theorem differenceTail_le_reciprocalTail_div
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a)) (n : ℕ) :
    DifferenceTail a n ≤ ReciprocalTail a n / ((a n : ℝ) - 1) := by
  let c : ℝ := 1 / ((a n : ℝ) - 1)
  have hAn : (0 : ℝ) < (a n : ℝ) - 1 := by
    have hcast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
    linarith
  have huShift := summable_seriesTail hu n
  have hdShift := summable_seriesTail (summable_differenceTerm ha hu hv) n
  have hterm : ∀ k : ℕ,
      DifferenceTerm a (k + n) ≤ ReciprocalTerm a (k + n) * c := by
    intro k
    have hnat : n ≤ k + n := by omega
    have hAk : (a n : ℝ) ≤ (a (k + n) : ℝ) := by
      exact_mod_cast hamono hnat
    have hAkpos : (0 : ℝ) < (a (k + n) : ℝ) := by
      have hcast : (2 : ℝ) ≤ (a (k + n) : ℝ) := by exact_mod_cast ha (k + n)
      linarith
    have hinv :
        1 / ((a (k + n) : ℝ) - 1) ≤ 1 / ((a n : ℝ) - 1) :=
      one_div_le_one_div_of_le hAn (sub_le_sub_right hAk 1)
    calc
      DifferenceTerm a (k + n) =
          ReciprocalTerm a (k + n) * (1 / ((a (k + n) : ℝ) - 1)) := by
        rw [DifferenceTerm, ReciprocalTerm]
        field_simp
      _ ≤ ReciprocalTerm a (k + n) * c :=
        mul_le_mul_of_nonneg_left hinv (by
          rw [ReciprocalTerm]
          positivity)
  have hsum := hdShift.tsum_le_tsum hterm (huShift.mul_right c)
  calc
    DifferenceTail a n ≤
        ∑' k : ℕ, ReciprocalTerm a (k + n) * c := hsum
    _ = ReciprocalTail a n * c := huShift.tsum_mul_right c
    _ = ReciprocalTail a n / ((a n : ℝ) - 1) := by
      simp only [c, div_eq_mul_inv, one_mul]

/-- The upper bound consumed by the local square recurrence, valid once
the reciprocal tail is at most one. -/
theorem differenceTail_le_one_div_sub_one
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a)) {n : ℕ}
    (hT : ReciprocalTail a n ≤ 1) :
    DifferenceTail a n ≤ 1 / ((a n : ℝ) - 1) := by
  have hden : 0 ≤ (1 : ℝ) / ((a n : ℝ) - 1) := by
    have hcast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
    exact (one_div_pos.mpr (by linarith)).le
  calc
    DifferenceTail a n ≤ ReciprocalTail a n / ((a n : ℝ) - 1) :=
      differenceTail_le_reciprocalTail_div ha hamono hu hv n
    _ ≤ 1 / ((a n : ℝ) - 1) := by
      have hinv : 0 ≤ ((a n : ℝ) - 1)⁻¹ := by
        simpa [one_div] using hden
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hT hinv

theorem reciprocalTail_tendsto_zero (a : ℕ → ℕ) :
    Tendsto (ReciprocalTail a) atTop (𝓝 0) :=
  seriesTail_tendsto_zero (ReciprocalTerm a)

theorem eventually_reciprocalTail_le_one (a : ℕ → ℕ) :
    ∀ᶠ n in atTop, ReciprocalTail a n ≤ 1 :=
  ((tendsto_order.1 (reciprocalTail_tendsto_zero a)).2 1 zero_lt_one).mono
    fun _ h ↦ h.le

/-! ## Arithmetic denominators -/

/-- Multiplication by the positive denominator clears a rational number. -/
theorem rat_den_mul_cast (q : ℚ) :
    (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
  rw [Rat.cast_def]
  field_simp [q.den_nz]

/-- Integer prefix product `P_n`. -/
def PrefixProduct (a : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∏ k ∈ Finset.range n, (a k : ℤ)

/-- Integer shifted prefix product `Q_n`. -/
def ShiftedPrefixProduct (a : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∏ k ∈ Finset.range n, ((a k : ℤ) - 1)

@[simp] theorem prefixProduct_zero (a : ℕ → ℕ) : PrefixProduct a 0 = 1 := by
  simp [PrefixProduct]

@[simp] theorem shiftedPrefixProduct_zero (a : ℕ → ℕ) :
    ShiftedPrefixProduct a 0 = 1 := by
  simp [ShiftedPrefixProduct]

theorem prefixProduct_succ (a : ℕ → ℕ) (n : ℕ) :
    PrefixProduct a (n + 1) = PrefixProduct a n * (a n : ℤ) := by
  simp [PrefixProduct, Finset.prod_range_succ]

theorem shiftedPrefixProduct_succ (a : ℕ → ℕ) (n : ℕ) :
    ShiftedPrefixProduct a (n + 1) =
      ShiftedPrefixProduct a n * ((a n : ℤ) - 1) := by
  simp [ShiftedPrefixProduct, Finset.prod_range_succ]

/-- The scaled tail used in the denominator argument. -/
noncomputable def ScaledDifference
    (C : ℤ) (a : ℕ → ℕ) (D : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((C * PrefixProduct a n * ShiftedPrefixProduct a n : ℤ) : ℝ) * D n

/-- The recurrence preserves integrality of the scaled tail.  This induction
is the denominator-clearing argument, isolated from the infinite-series
construction. -/
theorem scaledDifference_isInteger
    {a : ℕ → ℕ} {D : ℕ → ℝ} {C : ℤ}
    (ha : ∀ n, 2 ≤ a n)
    (hrec : ∀ n,
      D n = 1 / ((a n : ℝ) * ((a n : ℝ) - 1)) + D (n + 1))
    (hzero : ∃ z : ℤ, ScaledDifference C a D 0 = (z : ℝ)) :
    ∀ n, ∃ z : ℤ, ScaledDifference C a D n = (z : ℝ) := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      obtain ⟨z, hz⟩ := ih
      let x : ℝ := a n
      let m : ℝ := (C * PrefixProduct a n * ShiftedPrefixProduct a n : ℤ)
      have hx : 0 < x := by
        dsimp [x]
        exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
      have hx1 : 0 < x - 1 := by
        have hcast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
        dsimp [x]
        linarith
      have hxy : x * (x - 1) ≠ 0 := (mul_pos hx hx1).ne'
      have hrecMul : x * (x - 1) * D n =
          1 + x * (x - 1) * D (n + 1) := by
        have hr := hrec n
        change D n = 1 / (x * (x - 1)) + D (n + 1) at hr
        rw [hr]
        field_simp [hxy]
      refine ⟨((a n : ℤ) * ((a n : ℤ) - 1)) * z -
        C * PrefixProduct a n * ShiftedPrefixProduct a n, ?_⟩
      rw [ScaledDifference, prefixProduct_succ, shiftedPrefixProduct_succ]
      have hz' : m * D n = (z : ℝ) := by
        simpa [ScaledDifference, m] using hz
      calc
        ((C * (PrefixProduct a n * (a n : ℤ)) *
            (ShiftedPrefixProduct a n * ((a n : ℤ) - 1)) : ℤ) : ℝ) *
              D (n + 1) = (m * x * (x - 1)) * D (n + 1) := by
          simp only [m, x]
          push_cast
          ring
        _ = m * (x * (x - 1) * D (n + 1)) := by ring
        _ = m * (x * (x - 1) * D n - 1) := by
          rw [show x * (x - 1) * D (n + 1) =
            x * (x - 1) * D n - 1 by linarith [hrecMul]]
        _ = x * (x - 1) * (m * D n) - m := by ring
        _ = x * (x - 1) * (z : ℝ) - m := by rw [hz']
        _ = (((a n : ℤ) * ((a n : ℤ) - 1)) * z -
            C * PrefixProduct a n * ShiftedPrefixProduct a n : ℤ) := by
          simp only [x, m]
          push_cast
          ring

/-- At index zero, the difference tail is the difference of the two
rational total sums. -/
theorem differenceTail_zero_eq_rat
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {qu qv : ℚ}
    (hqu : ∑' n : ℕ, ReciprocalTerm a n = (qu : ℝ))
    (hqv : ∑' n : ℕ, ShiftedReciprocalTerm a n = (qv : ℝ)) :
    DifferenceTail a 0 = ((qv - qu : ℚ) : ℝ) := by
  have hdiff := shiftedTail_sub_reciprocalTail_eq_differenceTail ha hu hv 0
  calc
    DifferenceTail a 0 =
        ShiftedReciprocalTail a 0 - ReciprocalTail a 0 := hdiff.symm
    _ = (∑' n : ℕ, ShiftedReciprocalTerm a n) -
          ∑' n : ℕ, ReciprocalTerm a n := by
      simp [ShiftedReciprocalTail, ReciprocalTail, SeriesTail]
    _ = (qv : ℝ) - (qu : ℝ) := by rw [hqu, hqv]
    _ = ((qv - qu : ℚ) : ℝ) := by push_cast; rfl

/-- Rationality of both original sums supplies one positive integer scale
which makes every difference tail integral after multiplication by `P_nQ_n`.
-/
theorem exists_integral_scale_for_differenceTail
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {qu qv : ℚ}
    (hqu : ∑' n : ℕ, ReciprocalTerm a n = (qu : ℝ))
    (hqv : ∑' n : ℕ, ShiftedReciprocalTerm a n = (qv : ℝ)) :
    ∃ C : ℤ, 0 < C ∧
      ∀ n, ∃ z : ℤ,
        ScaledDifference C a (DifferenceTail a) n = (z : ℝ) := by
  let q : ℚ := qv - qu
  let C : ℤ := q.den
  have hC : 0 < C := by
    dsimp [C]
    exact_mod_cast q.den_pos
  have hd0 : DifferenceTail a 0 = (q : ℝ) := by
    exact differenceTail_zero_eq_rat ha hu hv hqu hqv
  have hzero : ∃ z : ℤ,
      ScaledDifference C a (DifferenceTail a) 0 = (z : ℝ) := by
    refine ⟨q.num, ?_⟩
    simp only [ScaledDifference, prefixProduct_zero, shiftedPrefixProduct_zero, mul_one]
    rw [hd0]
    simpa [C] using rat_den_mul_cast q
  exact ⟨C, hC,
    scaledDifference_isInteger ha
      (differenceTail_eq_add_succ ha hu hv) hzero⟩

theorem prefixProduct_pos
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    0 < PrefixProduct a n := by
  rw [PrefixProduct]
  apply Finset.prod_pos
  intro k _
  exact_mod_cast (lt_of_lt_of_le (by omega) (ha k))

theorem shiftedPrefixProduct_pos
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    0 < ShiftedPrefixProduct a n := by
  rw [ShiftedPrefixProduct]
  apply Finset.prod_pos
  intro k _
  have hk : (2 : ℤ) ≤ (a k : ℤ) := by exact_mod_cast ha k
  linarith

theorem shiftedPrefixProduct_le_prefixProduct
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    ShiftedPrefixProduct a n ≤ PrefixProduct a n := by
  induction n with
  | zero =>
      simp [ShiftedPrefixProduct, PrefixProduct]
  | succ n ih =>
      rw [shiftedPrefixProduct_succ, prefixProduct_succ]
      have hfactor_nonneg : (0 : ℤ) ≤ (a n : ℤ) - 1 := by
        have hk : (2 : ℤ) ≤ (a n : ℤ) := by exact_mod_cast ha n
        omega
      have hfactor_le : (a n : ℤ) - 1 ≤ (a n : ℤ) := by omega
      calc
        ShiftedPrefixProduct a n * ((a n : ℤ) - 1) ≤
            PrefixProduct a n * ((a n : ℤ) - 1) :=
          mul_le_mul_of_nonneg_right ih hfactor_nonneg
        _ ≤ PrefixProduct a n * (a n : ℤ) :=
          mul_le_mul_of_nonneg_left hfactor_le
            (le_of_lt (prefixProduct_pos ha n))

/-- A positive integral scaled tail is at least one. -/
theorem one_le_scaledDifference
    {a : ℕ → ℕ} {D : ℕ → ℝ} {C : ℤ}
    (ha : ∀ n, 2 ≤ a n) (hC : 0 < C)
    (hD : ∀ n, 0 < D n)
    (hint : ∀ n, ∃ z : ℤ, ScaledDifference C a D n = (z : ℝ))
    (n : ℕ) :
    1 ≤ ScaledDifference C a D n := by
  obtain ⟨z, hz⟩ := hint n
  have hfactor : 0 < C * PrefixProduct a n * ShiftedPrefixProduct a n :=
    mul_pos (mul_pos hC (prefixProduct_pos ha n)) (shiftedPrefixProduct_pos ha n)
  have hpos : 0 < ScaledDifference C a D n := by
    rw [ScaledDifference]
    exact mul_pos (by exact_mod_cast hfactor) (hD n)
  have hzpos : 0 < z := by
    exact_mod_cast (show (0 : ℝ) < (z : ℝ) by simpa [hz] using hpos)
  have hz1 : (1 : ℤ) ≤ z := by omega
  rw [hz]
  exact_mod_cast hz1

/-- We may replace `Q_n` by the larger `P_n`, yielding the square lower
bound consumed by `square_recurrence_local`. -/
theorem one_le_scale_mul_prefix_sq_mul_differenceTail
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {C : ℤ} (hC : 0 < C)
    (hint : ∀ n, ∃ z : ℤ,
      ScaledDifference C a (DifferenceTail a) n = (z : ℝ))
    (n : ℕ) :
    1 ≤ (C : ℝ) * (PrefixProduct a n : ℝ) ^ 2 * DifferenceTail a n := by
  have hbase := one_le_scaledDifference ha hC
    (differenceTail_pos ha hu hv) hint n
  have hCle : (0 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC.le
  have hPle : (0 : ℝ) ≤ (PrefixProduct a n : ℝ) := by
    exact_mod_cast (prefixProduct_pos ha n).le
  have hQle : (ShiftedPrefixProduct a n : ℝ) ≤ (PrefixProduct a n : ℝ) := by
    exact_mod_cast shiftedPrefixProduct_le_prefixProduct ha n
  have hDle : 0 ≤ DifferenceTail a n := differenceTail_nonneg ha n
  calc
    1 ≤ ScaledDifference C a (DifferenceTail a) n := hbase
    _ = (C : ℝ) * (PrefixProduct a n : ℝ) *
        (ShiftedPrefixProduct a n : ℝ) * DifferenceTail a n := by
      rw [ScaledDifference]
      push_cast
      rfl
    _ ≤ (C : ℝ) * (PrefixProduct a n : ℝ) *
        (PrefixProduct a n : ℝ) * DifferenceTail a n := by
      gcongr
    _ = (C : ℝ) * (PrefixProduct a n : ℝ) ^ 2 * DifferenceTail a n := by
      ring

theorem summable_reciprocalTerm_of_admissible
    {a : ℕ → ℕ} (ha : IsRationalPairSequence a) :
    Summable (ReciprocalTerm a) := by
  change Summable (fun n : ℕ ↦ (1 : ℝ) / (a n : ℝ))
  exact ha.2.2.1

theorem summable_shiftedReciprocalTerm_of_admissible
    {a : ℕ → ℕ} (ha : IsRationalPairSequence a) :
    Summable (ShiftedReciprocalTerm a) := by
  change Summable (fun n : ℕ ↦ (1 : ℝ) / ((a n : ℝ) - 1))
  exact ha.2.2.2.1

/-- The arithmetic package extracted directly from an admissible sequence. -/
theorem admissible_has_integral_difference_scale
    {a : ℕ → ℕ} (ha : IsRationalPairSequence a) :
    ∃ C : ℤ, 0 < C ∧
      ∀ n, ∃ z : ℤ,
        ScaledDifference C a (DifferenceTail a) n = (z : ℝ) := by
  obtain ⟨qu, hqu⟩ := ha.2.2.2.2.1
  obtain ⟨qv, hqv⟩ := ha.2.2.2.2.2
  apply exists_integral_scale_for_differenceTail
    (two_le_of_isRationalPairSequence ha)
    (summable_reciprocalTerm_of_admissible ha)
    (summable_shiftedReciprocalTerm_of_admissible ha)
  · change (∑' n : ℕ, (1 : ℝ) / (a n : ℝ)) = (qu : ℝ)
    exact hqu
  · change (∑' n : ℕ, (1 : ℝ) / ((a n : ℝ) - 1)) = (qv : ℝ)
    exact hqv

end Erdos265

/-!
# The square recurrence

This file formalizes the local two-case estimate that absorbs irregular growth.
It is stated for positive real variables so that the arithmetic denominator
argument can be connected later without duplicating the analytic algebra.
-/

namespace Erdos265

private theorem sq_div_sqrt {x D : ℝ} (hD : 0 < D) :
    (x / Real.sqrt D) ^ 2 = x ^ 2 / D := by
  rw [div_pow, Real.sq_sqrt hD.le]

private theorem one_div_sqrt_le {q P D : ℝ}
    (hq : 0 ≤ q) (hP : 0 ≤ P) (hD : 0 < D)
    (hscaled : 1 ≤ q * P ^ 2 * D) :
    1 / Real.sqrt D ≤ Real.sqrt q * P := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  rw [sq_div_sqrt hD]
  simp only [one_pow, mul_pow, Real.sq_sqrt hq]
  rw [div_le_iff₀ hD]
  nlinarith [sq_nonneg P]

/-- The local estimate used in the report.

`D = 1/(a(a-1)) + Dnext` is the tail decomposition.  The two scaled lower
bounds are the real form of the integer-denominator estimates at `n` and
`n+1`.  The upper bound `D ≤ 1/(a-1)` follows later from monotonicity of the
integer sequence.
-/
theorem square_recurrence_local
    {q P a D Dnext : ℝ}
    (hq : 1 ≤ q) (hP : 0 < P) (ha : 2 ≤ a)
    (hD : 0 < D) (hDnext : 0 < Dnext)
    (hscaled : 1 ≤ q * P ^ 2 * D)
    (hscaled_next : 1 ≤ q * (P * a) ^ 2 * Dnext)
    (hdecomp : D = 1 / (a * (a - 1)) + Dnext)
    (hupper : D ≤ 1 / (a - 1)) :
    P * a / Real.sqrt Dnext ≤
      4 * Real.sqrt q * (P / Real.sqrt D) ^ 2 := by
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hP0 : 0 ≤ P := hP.le
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have ha1 : 0 < a - 1 := by linarith
  have hden : 0 < a * (a - 1) := mul_pos (by linarith) ha1
  have hsqrtq0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hsqrtD0 : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
  have hsqrtDnext0 : 0 < Real.sqrt Dnext := Real.sqrt_pos.2 hDnext
  by_cases hhead : D / 2 ≤ 1 / (a * (a - 1))
  · have hclear : D / 2 * (a * (a - 1)) ≤ 1 :=
      (le_div_iff₀ hden).1 hhead
    have ha_sq_le : a ^ 2 ≤ 4 / D := by
      rw [le_div_iff₀ hD]
      nlinarith [mul_nonneg hD.le (sq_nonneg (a - 2))]
    have hinv_next : 1 / Real.sqrt Dnext ≤ Real.sqrt q * (P * a) :=
      one_div_sqrt_le hq0 (mul_nonneg hP0 ha0) hDnext hscaled_next
    calc
      P * a / Real.sqrt Dnext = (P * a) * (1 / Real.sqrt Dnext) := by ring
      _ ≤ (P * a) * (Real.sqrt q * (P * a)) :=
        mul_le_mul_of_nonneg_left hinv_next (mul_nonneg hP0 ha0)
      _ = Real.sqrt q * P ^ 2 * a ^ 2 := by ring
      _ ≤ Real.sqrt q * P ^ 2 * (4 / D) :=
        mul_le_mul_of_nonneg_left ha_sq_le (mul_nonneg hsqrtq0 (sq_nonneg P))
      _ = 4 * Real.sqrt q * (P / Real.sqrt D) ^ 2 := by
        rw [sq_div_sqrt hD]
        ring
  · have hhead_lt : 1 / (a * (a - 1)) < D / 2 := lt_of_not_ge hhead
    have hD_half : D / 2 < Dnext := by linarith [hdecomp]
    have hupper_clear : D * (a - 1) ≤ 1 :=
      (le_div_iff₀ ha1).1 hupper
    have hD_le_one : D ≤ 1 := by
      have : 1 ≤ a - 1 := by linarith
      nlinarith [mul_nonneg hD.le (sub_nonneg.mpr this)]
    have hDa : D * a ≤ 2 := by nlinarith
    have hDa0 : 0 ≤ D * a := mul_nonneg hD.le ha0
    have hDa_sq : (D * a) ^ 2 ≤ (2 : ℝ) ^ 2 :=
      (sq_le_sq₀ hDa0 (by norm_num)).2 hDa
    have hleft_poly : P ^ 2 * a ^ 2 * D ^ 2 ≤ 4 * P ^ 2 := by
      have hP2 := sq_nonneg P
      nlinarith
    have hqP2_pos : 0 < q * P ^ 2 :=
      mul_pos (lt_of_lt_of_le (by norm_num) hq) (sq_pos_of_pos hP)
    have hhalf_scaled : 1 < 2 * (q * P ^ 2 * Dnext) := by
      have hm := mul_lt_mul_of_pos_left hD_half hqP2_pos
      nlinarith [hscaled]
    have hone_scaled : 1 ≤ 4 * (q * P ^ 2 * Dnext) := by linarith
    have hright_poly : 4 * P ^ 2 ≤ 16 * q * P ^ 4 * Dnext := by
      have hfourP : 0 ≤ (4 : ℝ) * P ^ 2 := mul_nonneg (by norm_num) (sq_nonneg P)
      have hm := mul_le_mul_of_nonneg_left hone_scaled hfourP
      nlinarith [sq_nonneg P]
    have hsquares :
        (P * a / Real.sqrt Dnext) ^ 2 ≤
          (4 * Real.sqrt q * (P / Real.sqrt D) ^ 2) ^ 2 := by
      calc
        (P * a / Real.sqrt Dnext) ^ 2 = P ^ 2 * a ^ 2 / Dnext := by
          rw [sq_div_sqrt hDnext]
          ring
        _ ≤ 16 * q * P ^ 4 / D ^ 2 := by
          rw [div_le_div_iff₀ hDnext (sq_pos_of_pos hD)]
          exact hleft_poly.trans hright_poly
        _ = (4 * Real.sqrt q * (P / Real.sqrt D) ^ 2) ^ 2 := by
          rw [sq_div_sqrt hD]
          simp only [mul_pow, Real.sq_sqrt hq0]
          ring
    exact (sq_le_sq₀ (by positivity) (by positivity)).1 hsquares

end Erdos265

/-!
# The tail envelope and its quadratic recurrence

This file connects the arithmetic lower bound to the local two-case estimate.
-/

namespace Erdos265

/-- `H_n = P_n / sqrt(D_n)`. -/
noncomputable def TailEnvelope (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (PrefixProduct a n : ℝ) / Real.sqrt (DifferenceTail a n)

theorem tailEnvelope_pos
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a)) (n : ℕ) :
    0 < TailEnvelope a n := by
  rw [TailEnvelope]
  exact div_pos (by exact_mod_cast prefixProduct_pos ha n)
    (Real.sqrt_pos.2 (differenceTail_pos ha hu hv n))

theorem one_le_tailEnvelope_of_tail_le_one
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {n : ℕ} (hT : ReciprocalTail a n ≤ 1) :
    1 ≤ TailEnvelope a n := by
  have hDpos := differenceTail_pos ha hu hv n
  have hDone : DifferenceTail a n ≤ 1 := by
    have hupper := differenceTail_le_one_div_sub_one ha hamono hu hv hT
    have hsub : (1 : ℝ) ≤ (a n : ℝ) - 1 := by
      have hcast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
      linarith
    have hinv : (1 : ℝ) / ((a n : ℝ) - 1) ≤ 1 := by
      simpa using one_div_le_one_div_of_le zero_lt_one hsub
    exact hupper.trans hinv
  have hsqrt : Real.sqrt (DifferenceTail a n) ≤ 1 :=
    Real.sqrt_le_one.mpr hDone
  have hPone : (1 : ℝ) ≤ (PrefixProduct a n : ℝ) := by
    have hz : (1 : ℤ) ≤ PrefixProduct a n := by
      have := prefixProduct_pos ha n
      omega
    exact_mod_cast hz
  rw [TailEnvelope, le_div_iff₀ (Real.sqrt_pos.2 hDpos)]
  simpa using hsqrt.trans hPone

theorem prefixProduct_le_tailEnvelope_of_tail_le_one
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {n : ℕ} (hT : ReciprocalTail a n ≤ 1) :
    (PrefixProduct a n : ℝ) ≤ TailEnvelope a n := by
  have hDpos := differenceTail_pos ha hu hv n
  have hDone : DifferenceTail a n ≤ 1 := by
    have hupper := differenceTail_le_one_div_sub_one ha hamono hu hv hT
    have hsub : (1 : ℝ) ≤ (a n : ℝ) - 1 := by
      have hcast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
      linarith
    have hinv : (1 : ℝ) / ((a n : ℝ) - 1) ≤ 1 := by
      simpa using one_div_le_one_div_of_le zero_lt_one hsub
    exact hupper.trans hinv
  have hsqrt : Real.sqrt (DifferenceTail a n) ≤ 1 :=
    Real.sqrt_le_one.mpr hDone
  have hP : (0 : ℝ) ≤ (PrefixProduct a n : ℝ) := by
    exact_mod_cast (prefixProduct_pos ha n).le
  rw [TailEnvelope, le_div_iff₀ (Real.sqrt_pos.2 hDpos)]
  simpa using mul_le_of_le_one_right hP hsqrt

theorem current_le_tailEnvelope_succ_of_tail_le_one
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {n : ℕ} (hTnext : ReciprocalTail a (n + 1) ≤ 1) :
    (a n : ℝ) ≤ TailEnvelope a (n + 1) := by
  have hPone : (1 : ℝ) ≤ (PrefixProduct a n : ℝ) := by
    have hz : (1 : ℤ) ≤ PrefixProduct a n := by
      have := prefixProduct_pos ha n
      omega
    exact_mod_cast hz
  have ha0 : (0 : ℝ) ≤ (a n : ℝ) := by positivity
  calc
    (a n : ℝ) = 1 * (a n : ℝ) := by ring
    _ ≤ (PrefixProduct a n : ℝ) * (a n : ℝ) :=
      mul_le_mul_of_nonneg_right hPone ha0
    _ = (PrefixProduct a (n + 1) : ℤ) := by
      rw [prefixProduct_succ]
      push_cast
      rfl
    _ ≤ TailEnvelope a (n + 1) :=
      prefixProduct_le_tailEnvelope_of_tail_le_one ha hamono hu hv hTnext

/-- Once `T_n ≤ 1`, the arithmetic scale and the local two-case estimate give
the advertised quadratic recurrence. -/
theorem tailEnvelope_square_recurrence_of_tail_le_one
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {C : ℤ} (hC : 0 < C)
    (hint : ∀ n, ∃ z : ℤ,
      ScaledDifference C a (DifferenceTail a) n = (z : ℝ))
    {n : ℕ} (hT : ReciprocalTail a n ≤ 1) :
    TailEnvelope a (n + 1) ≤
      4 * Real.sqrt (C : ℝ) * (TailEnvelope a n) ^ 2 := by
  have hC1z : (1 : ℤ) ≤ C := by omega
  have hC1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1z
  have hPpos : (0 : ℝ) < (PrefixProduct a n : ℝ) := by
    exact_mod_cast prefixProduct_pos ha n
  have han : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
  have hD := differenceTail_pos ha hu hv n
  have hDnext := differenceTail_pos ha hu hv (n + 1)
  have hscaled := one_le_scale_mul_prefix_sq_mul_differenceTail
    ha hu hv hC hint n
  have hscaledNext := one_le_scale_mul_prefix_sq_mul_differenceTail
    ha hu hv hC hint (n + 1)
  have hdecomp : DifferenceTail a n =
      1 / ((a n : ℝ) * ((a n : ℝ) - 1)) + DifferenceTail a (n + 1) := by
    rw [differenceTail_eq_add_succ ha hu hv n, DifferenceTerm]
  have hupper := differenceTail_le_one_div_sub_one ha hamono hu hv hT
  have hlocal := square_recurrence_local hC1 hPpos han hD hDnext
    hscaled (by
      rw [prefixProduct_succ] at hscaledNext
      push_cast at hscaledNext
      simpa only [Int.cast_natCast] using hscaledNext)
    hdecomp hupper
  rw [TailEnvelope, TailEnvelope, prefixProduct_succ]
  push_cast
  exact hlocal

/-- The recurrence holds eventually because every summable tail tends to
zero. -/
theorem eventually_tailEnvelope_square_recurrence
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {C : ℤ} (hC : 0 < C)
    (hint : ∀ n, ∃ z : ℤ,
      ScaledDifference C a (DifferenceTail a) n = (z : ℝ)) :
    ∀ᶠ n in Filter.atTop,
      TailEnvelope a (n + 1) ≤
        4 * Real.sqrt (C : ℝ) * (TailEnvelope a n) ^ 2 :=
  (eventually_reciprocalTail_le_one a).mono fun _ hT ↦
    tailEnvelope_square_recurrence_of_tail_le_one ha hamono hu hv hC hint hT

theorem eventually_one_le_tailEnvelope
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a)) :
    ∀ᶠ n in Filter.atTop, 1 ≤ TailEnvelope a n :=
  (eventually_reciprocalTail_le_one a).mono fun _ hT ↦
    one_le_tailEnvelope_of_tail_le_one ha hamono hu hv hT

end Erdos265

/-!
# Regularizing a quadratic recurrence

The quantity `log (K * H n) / 2^n` removes the quadratic scale from a
recurrence `H (n+1) ≤ K * H n ^ 2`.  Its monotonicity is the first global
step in the irregular-growth argument.
-/

open Filter Topology

namespace Erdos265

/-- The logarithmically normalized envelope attached to a quadratic
recurrence. -/
noncomputable def NormalizedEnvelope (K : ℝ) (H : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.log (K * H n) / (2 : ℝ) ^ n

/-- Binary logarithmic growth for a positive real sequence. -/
noncomputable def BinaryLogRatio (H : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.log (H n) / (2 : ℝ) ^ n

/-- A positive quadratic recurrence becomes antitone after logarithmic
normalization. -/
theorem normalizedEnvelope_antitone
    {K : ℝ} {H : ℕ → ℝ}
    (hK : 0 < K) (hH : ∀ n, 0 < H n)
    (hrec : ∀ n, H (n + 1) ≤ K * (H n) ^ 2) :
    Antitone (NormalizedEnvelope K H) := by
  apply antitone_nat_of_succ_le
  intro n
  have hKH : 0 < K * H n := mul_pos hK (hH n)
  have hKHnext : 0 < K * H (n + 1) := mul_pos hK (hH (n + 1))
  have hquad : K * H (n + 1) ≤ (K * H n) ^ 2 := by
    calc
      K * H (n + 1) ≤ K * (K * (H n) ^ 2) :=
        mul_le_mul_of_nonneg_left (hrec n) hK.le
      _ = (K * H n) ^ 2 := by ring
  have hlog : Real.log (K * H (n + 1)) ≤ 2 * Real.log (K * H n) := by
    have := Real.log_le_log hKHnext hquad
    simpa [Real.log_pow] using this
  have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  unfold NormalizedEnvelope
  rw [pow_succ]
  rw [div_le_div_iff₀ (mul_pos hpow (by norm_num)) hpow]
  have hm := mul_le_mul_of_nonneg_right hlog hpow.le
  nlinarith

/-- If the normalized envelope is bounded below, it has a finite real
limit.  In the application the lower bound is zero. -/
theorem normalizedEnvelope_hasLimit
    {K : ℝ} {H : ℕ → ℝ}
    (hK : 0 < K) (hH : ∀ n, 0 < H n)
    (hrec : ∀ n, H (n + 1) ≤ K * (H n) ^ 2)
    (hbelow : BddBelow (Set.range (NormalizedEnvelope K H))) :
    ∃ ell : ℝ, Tendsto (NormalizedEnvelope K H) atTop (𝓝 ell) := by
  refine ⟨⨅ n : ℕ, NormalizedEnvelope K H n, ?_⟩
  exact tendsto_atTop_ciInf (normalizedEnvelope_antitone hK hH hrec) hbelow

/-- Multiplication by the fixed recurrence constant contributes only
`log K / 2^n`, hence does not change the normalized limit. -/
theorem normalizedEnvelope_tendsto_iff_binaryLogRatio
    {K ell : ℝ} {H : ℕ → ℝ}
    (hK : 0 < K) (hH : ∀ n, 0 < H n) :
    Tendsto (NormalizedEnvelope K H) atTop (𝓝 ell) ↔
      Tendsto (BinaryLogRatio H) atTop (𝓝 ell) := by
  have hpow : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hvanish :
      Tendsto (fun n : ℕ ↦ Real.log K / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hsplit : ∀ n,
      NormalizedEnvelope K H n =
        Real.log K / (2 : ℝ) ^ n + BinaryLogRatio H n := by
    intro n
    rw [NormalizedEnvelope, BinaryLogRatio, Real.log_mul hK.ne' (hH n).ne']
    ring
  constructor
  · intro h
    have hsub := h.sub hvanish
    convert hsub using 1
    · funext n
      rw [hsplit]
      ring
    · simp
  · intro h
    have hadd := hvanish.add h
    convert hadd using 1
    · funext n
      exact hsplit n
    · simp

/-- If `A n ≤ H (n+1)` and the envelope has normalized limit zero, then so
does `A`.  The index shift costs exactly a factor of two. -/
theorem binaryLogRatio_tendsto_zero_of_le_succ
    {A H : ℕ → ℝ}
    (hA : ∀ n, 1 ≤ A n)
    (hAH : ∀ n, A n ≤ H (n + 1))
    (hlim : Tendsto (BinaryLogRatio H) atTop (𝓝 0)) :
    Tendsto (BinaryLogRatio A) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ ↦ BinaryLogRatio H (n + 1)) atTop (𝓝 0) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hupperlim :
      Tendsto (fun n : ℕ ↦ 2 * BinaryLogRatio H (n + 1)) atTop (𝓝 0) := by
    simpa using hshift.const_mul 2
  apply squeeze_zero
  · intro n
    rw [BinaryLogRatio]
    exact div_nonneg (Real.log_nonneg (hA n)) (by positivity)
  · intro n
    have hApos : 0 < A n := lt_of_lt_of_le zero_lt_one (hA n)
    have hHpos : 0 < H (n + 1) := hApos.trans_le (hAH n)
    have hlog : Real.log (A n) ≤ Real.log (H (n + 1)) :=
      Real.log_le_log hApos (hAH n)
    have hp : 0 ≤ (2 : ℝ) ^ n := by positivity
    calc
      BinaryLogRatio A n ≤ Real.log (H (n + 1)) / (2 : ℝ) ^ n :=
        div_le_div_of_nonneg_right hlog hp
      _ = 2 * BinaryLogRatio H (n + 1) := by
        rw [BinaryLogRatio, pow_succ]
        field_simp
  · exact hupperlim

/-- An eventual quadratic recurrence may be shifted to an everywhere-valid
one.  If its normalized logarithm is eventually nonnegative, the shifted
sequence has a nonnegative finite limit. -/
theorem eventual_quadratic_has_shifted_limit
    {K : ℝ} {H : ℕ → ℝ}
    (hK : 0 < K) (hH : ∀ n, 0 < H n)
    (hrec : ∀ᶠ n in atTop, H (n + 1) ≤ K * (H n) ^ 2)
    (hge : ∀ᶠ n in atTop, 1 ≤ K * H n) :
    ∃ N : ℕ, ∃ ell : ℝ, 0 ≤ ell ∧
      Tendsto (BinaryLogRatio (fun j ↦ H (j + N))) atTop (𝓝 ell) := by
  obtain ⟨Nr, hNr⟩ := (eventually_atTop.1 hrec)
  obtain ⟨Ng, hNg⟩ := (eventually_atTop.1 hge)
  let N := max Nr Ng
  let HS : ℕ → ℝ := fun j ↦ H (j + N)
  have hrecS : ∀ j, HS (j + 1) ≤ K * (HS j) ^ 2 := by
    intro j
    dsimp [HS]
    have hNrN : Nr ≤ N := by simp [N]
    have hNle : N ≤ j + N := by omega
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hNr (j + N) (hNrN.trans hNle)
  have hHS : ∀ j, 0 < HS j := fun j ↦ hH (j + N)
  have hgeS : ∀ j, 1 ≤ K * HS j := by
    intro j
    have hNgN : Ng ≤ N := by simp [N]
    have hNle : N ≤ j + N := by omega
    exact hNg (j + N) (hNgN.trans hNle)
  have hnonneg : ∀ j, 0 ≤ NormalizedEnvelope K HS j := by
    intro j
    rw [NormalizedEnvelope]
    exact div_nonneg (Real.log_nonneg (hgeS j)) (by positivity)
  have hbelow : BddBelow (Set.range (NormalizedEnvelope K HS)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact hnonneg j
  obtain ⟨ell, hell⟩ := normalizedEnvelope_hasLimit hK hHS hrecS hbelow
  have hell0 : 0 ≤ ell :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hell hnonneg
  exact ⟨N, ell, hell0,
    (normalizedEnvelope_tendsto_iff_binaryLogRatio hK hHS).1 hell⟩

end Erdos265

/-!
# Consequences of a positive normalized envelope limit

The first bounds in this file turn growth of `H_n` into growth of the
cumulative logarithms of `a_n`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos265

/-- `B_n = ∑_{k≤n} log a_k`. -/
noncomputable def CumulativeLog (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), Real.log (a k : ℝ)

theorem log_prefixProduct
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    Real.log (PrefixProduct a n : ℝ) =
      ∑ k ∈ Finset.range n, Real.log (a k : ℝ) := by
  rw [PrefixProduct]
  push_cast
  apply Real.log_prod
  intro k _
  have hk : (0 : ℝ) < (a k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha k))
  exact hk.ne'

theorem differenceTerm_ge_inv_sq
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    1 / (a n : ℝ) ^ 2 ≤ DifferenceTerm a n := by
  have hA : (0 : ℝ) < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  have hA1 : (0 : ℝ) < (a n : ℝ) - 1 := by
    have hcast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
    linarith
  rw [DifferenceTerm]
  rw [div_le_div_iff₀ (sq_pos_of_pos hA) (mul_pos hA hA1)]
  nlinarith

theorem inv_sq_le_differenceTail
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a)) (n : ℕ) :
    1 / (a n : ℝ) ^ 2 ≤ DifferenceTail a n := by
  rw [differenceTail_eq_add_succ ha hu hv n]
  exact (differenceTerm_ge_inv_sq ha n).trans
    (le_add_of_nonneg_right (differenceTail_nonneg ha (n + 1)))

/-- The head term of `D_n` implies `H_n ≤ P_n a_n`. -/
theorem tailEnvelope_le_prefix_mul_current
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a)) (n : ℕ) :
    TailEnvelope a n ≤ (PrefixProduct a n : ℝ) * (a n : ℝ) := by
  have hA : (0 : ℝ) < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  have hDpos := differenceTail_pos ha hu hv n
  have hlow := inv_sq_le_differenceTail ha hu hv n
  have hlow' : (1 / (a n : ℝ)) ^ 2 ≤ DifferenceTail a n := by
    simpa [div_pow] using hlow
  have hsqrt : 1 / (a n : ℝ) ≤ Real.sqrt (DifferenceTail a n) := by
    calc
      1 / (a n : ℝ) = Real.sqrt ((1 / (a n : ℝ)) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hA)]
      _ ≤ Real.sqrt (DifferenceTail a n) := Real.sqrt_le_sqrt hlow'
  have hone : 1 ≤ (a n : ℝ) * Real.sqrt (DifferenceTail a n) := by
    have hm := mul_le_mul_of_nonneg_left hsqrt hA.le
    field_simp at hm
    exact hm
  have hP : (0 : ℝ) ≤ (PrefixProduct a n : ℝ) := by
    exact_mod_cast (prefixProduct_pos ha n).le
  rw [TailEnvelope, div_le_iff₀ (Real.sqrt_pos.2 hDpos)]
  calc
    (PrefixProduct a n : ℝ) = (PrefixProduct a n : ℝ) * 1 := by ring
    _ ≤ (PrefixProduct a n : ℝ) *
        ((a n : ℝ) * Real.sqrt (DifferenceTail a n)) :=
      mul_le_mul_of_nonneg_left hone hP
    _ = (PrefixProduct a n : ℝ) * (a n : ℝ) *
        Real.sqrt (DifferenceTail a n) := by ring

theorem log_tailEnvelope_le_cumulativeLog
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a)) (n : ℕ) :
    Real.log (TailEnvelope a n) ≤ CumulativeLog a n := by
  have hHpos := tailEnvelope_pos ha hu hv n
  have hle := tailEnvelope_le_prefix_mul_current ha hu hv n
  have hlog := Real.log_le_log hHpos hle
  have han0 : (a n : ℝ) ≠ 0 := by
    have hcast : (0 : ℝ) < (a n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
    exact hcast.ne'
  rw [Real.log_mul (by exact_mod_cast (prefixProduct_pos ha n).ne')
    han0] at hlog
  rw [log_prefixProduct ha n] at hlog
  simpa [CumulativeLog, Finset.sum_range_succ] using hlog

/-- Monotonicity of `a` bounds its first `n+1` logarithms by the last one. -/
theorem cumulativeLog_le_count_mul_log
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a) (n : ℕ) :
    CumulativeLog a n ≤ (n + 1 : ℕ) * Real.log (a n : ℝ) := by
  rw [CumulativeLog]
  calc
    (∑ k ∈ Finset.range (n + 1), Real.log (a k : ℝ)) ≤
        ∑ _k ∈ Finset.range (n + 1), Real.log (a n : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := by simpa using Finset.mem_range.1 hk
      have hak : (0 : ℝ) < (a k : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by omega) (ha k))
      exact Real.log_le_log hak (by exact_mod_cast hamono hkn)
    _ = (n + 1 : ℕ) * Real.log (a n : ℝ) := by simp

/-- A fixed shift does not change the fact that an exponential dominates a
quadratic polynomial. -/
theorem shifted_square_div_two_pow_tendsto_zero (N : ℕ) :
    Tendsto
      (fun j : ℕ ↦ ((j + N + 1 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ j)
      atTop (𝓝 0) := by
  let d : ℝ := N + 1
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2
    (show (1 : ℝ) < 2 by norm_num)
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1
    (show (1 : ℝ) < 2 by norm_num)
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0
    (show (1 : ℝ) < 2 by norm_num)
  have hsum := (h2.add (h1.const_mul (2 * d))).add (h0.const_mul (d ^ 2))
  convert hsum using 1
  · funext j
    dsimp [d]
    push_cast
    field_simp
    ring
  · simp

/-- A positive normalized limit for the shifted tail envelope forces the
eventual elementary lower bound `exp n ≤ a_n`.  This is the first
regularization consequence used to control the whole reciprocal tail. -/
theorem positive_shifted_envelope_limit_forces_exp_growth
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {N : ℕ} {ell : ℝ} (hell : 0 < ell)
    (hlim : Tendsto
      (BinaryLogRatio (fun j ↦ TailEnvelope a (j + N))) atTop (𝓝 ell)) :
    ∀ᶠ m : ℕ in atTop, Real.exp (m : ℝ) ≤ (a m : ℝ) := by
  have hhalf : ell / 2 < ell := by linarith
  have hlarge : ∀ᶠ j in atTop,
      ell / 2 < BinaryLogRatio (fun r ↦ TailEnvelope a (r + N)) j :=
    (tendsto_order.1 hlim).1 _ hhalf
  have hsmall : ∀ᶠ j in atTop,
      ((j + N + 1 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ j < ell / 2 :=
    (tendsto_order.1 (shifted_square_div_two_pow_tendsto_zero N)).2
      _ (half_pos hell)
  have hshifted : ∀ᶠ j in atTop,
      Real.exp ((j + N : ℕ) : ℝ) ≤ (a (j + N) : ℝ) := by
    filter_upwards [hlarge, hsmall] with j hjlarge hjsmall
    let m : ℕ := j + N
    have hp : 0 < (2 : ℝ) ^ j := by positivity
    have hlogH : ell / 2 * (2 : ℝ) ^ j <
        Real.log (TailEnvelope a m) := by
      change ell / 2 <
        Real.log (TailEnvelope a (j + N)) / (2 : ℝ) ^ j at hjlarge
      have := (lt_div_iff₀ hp).1 hjlarge
      simpa [m] using this
    have hHB := log_tailEnvelope_le_cumulativeLog ha hu hv m
    have hBlog := cumulativeLog_le_count_mul_log ha hamono m
    have hpoly : ((m + 1 : ℕ) : ℝ) ^ 2 < ell / 2 * (2 : ℝ) ^ j := by
      rw [div_lt_iff₀ hp] at hjsmall
      simpa [m, Nat.add_assoc] using hjsmall
    have hmnonneg : (0 : ℝ) ≤ m := by positivity
    have hm1pos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hmprod : (m : ℝ) * (m + 1 : ℕ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
      have hmle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
        norm_num
      nlinarith
    have hmul : (m : ℝ) * (m + 1 : ℕ) <
        ((m + 1 : ℕ) : ℝ) * Real.log (a m : ℝ) :=
      lt_of_le_of_lt hmprod
        (hpoly.trans (hlogH.trans_le (hHB.trans hBlog)))
    have hmlog : (m : ℝ) ≤ Real.log (a m : ℝ) := by
      have hmul' : ((m + 1 : ℕ) : ℝ) * (m : ℝ) <
          ((m + 1 : ℕ) : ℝ) * Real.log (a m : ℝ) := by
        simpa [mul_comm] using hmul
      nlinarith
    exact (Real.le_log_iff_exp_le (by
      have hcast : (2 : ℝ) ≤ (a m : ℝ) := by exact_mod_cast ha m
      linarith)).1 hmlog
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hshifted
  filter_upwards [eventually_ge_atTop (J + N)] with m hm
  have hNm : N ≤ m := by omega
  let j := m - N
  have hj : J ≤ j := by
    dsimp [j]
    omega
  have he := hJ j hj
  simpa [j, Nat.sub_add_cancel hNm] using he

theorem exp_neg_one_pow (m : ℕ) :
    Real.exp (-1) ^ m = 1 / Real.exp (m : ℝ) := by
  rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
  congr 1
  ring

/-- Once `a_m ≥ exp m`, split the reciprocal tail at
`M = ceil(log a_n)`.  The first `M` terms use monotonicity and the remainder
is bounded by a geometric series. -/
theorem reciprocalTail_le_ceilLog_add_geometric_div
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    {N n : ℕ}
    (hExp : ∀ m ≥ N, Real.exp (m : ℝ) ≤ (a m : ℝ))
    (hn : N ≤ n) :
    ReciprocalTail a n ≤
      ((Nat.ceil (Real.log (a n : ℝ)) : ℝ) +
        (1 - Real.exp (-1))⁻¹) / (a n : ℝ) := by
  let M : ℕ := Nat.ceil (Real.log (a n : ℝ))
  let r : ℝ := Real.exp (-1)
  have hA : (0 : ℝ) < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  have hlog0 : 0 ≤ Real.log (a n : ℝ) :=
    Real.log_nonneg (by
      have hcast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
      linarith)
  have hMlog : Real.log (a n : ℝ) ≤ (M : ℝ) := by
    simpa [M] using Nat.le_ceil (Real.log (a n : ℝ))
  have ha_expM : (a n : ℝ) ≤ Real.exp (M : ℝ) :=
    (Real.log_le_iff_le_exp hA).1 hMlog
  have hrpos : 0 ≤ r := (Real.exp_pos _).le
  have hrlt : r < 1 := by
    change Real.exp (-1) < 1
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hgeom : Summable (fun k : ℕ ↦ r ^ k) :=
    summable_geometric_of_lt_one hrpos hrlt
  have huShift := summable_seriesTail hu n
  have hsplit : ReciprocalTail a n =
      (∑ k ∈ Finset.range M, ReciprocalTerm a (k + n)) +
        ∑' k : ℕ, ReciprocalTerm a (k + M + n) := by
    rw [ReciprocalTail, SeriesTail]
    simpa [Nat.add_assoc] using (huShift.sum_add_tsum_nat_add M).symm
  have hhead :
      (∑ k ∈ Finset.range M, ReciprocalTerm a (k + n)) ≤
        (M : ℝ) / (a n : ℝ) := by
    calc
      (∑ k ∈ Finset.range M, ReciprocalTerm a (k + n)) ≤
          ∑ _k ∈ Finset.range M, (1 : ℝ) / (a n : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        have hmono : (a n : ℝ) ≤ (a (k + n) : ℝ) := by
          exact_mod_cast hamono (by omega : n ≤ k + n)
        rw [ReciprocalTerm]
        exact one_div_le_one_div_of_le hA hmono
      _ = (M : ℝ) / (a n : ℝ) := by simp [div_eq_mul_inv]
  have htailTerm : ∀ k : ℕ,
      ReciprocalTerm a (k + M + n) ≤ r ^ (k + M) := by
    intro k
    let i : ℕ := k + M + n
    have hiN : N ≤ i := by dsimp [i]; omega
    have hgrowth := hExp i hiN
    have hexp_le : Real.exp ((k + M : ℕ) : ℝ) ≤ Real.exp (i : ℝ) := by
      apply Real.exp_le_exp.mpr
      norm_num [i]
    have hpoweq : r ^ (k + M) = 1 / Real.exp ((k + M : ℕ) : ℝ) := by
      exact exp_neg_one_pow (k + M)
    calc
      ReciprocalTerm a (k + M + n) = 1 / (a i : ℝ) := by
        simp [ReciprocalTerm, i]
      _ ≤ 1 / Real.exp (i : ℝ) :=
        one_div_le_one_div_of_le (Real.exp_pos _) hgrowth
      _ ≤ 1 / Real.exp ((k + M : ℕ) : ℝ) :=
        one_div_le_one_div_of_le (Real.exp_pos _) hexp_le
      _ = r ^ (k + M) := hpoweq.symm
  have hgeomShift : Summable (fun k : ℕ ↦ r ^ (k + M)) := by
    simpa using summable_seriesTail hgeom M
  have htail :
      (∑' k : ℕ, ReciprocalTerm a (k + M + n)) ≤
        r ^ M * (1 - r)⁻¹ := by
    calc
      (∑' k : ℕ, ReciprocalTerm a (k + M + n)) ≤
          ∑' k : ℕ, r ^ (k + M) :=
        (summable_seriesTail (summable_seriesTail hu n) M).tsum_le_tsum
          htailTerm hgeomShift
      _ = ∑' k : ℕ, r ^ k * r ^ M := by
        apply tsum_congr
        intro k
        rw [← pow_add]
      _ = (∑' k : ℕ, r ^ k) * r ^ M := hgeom.tsum_mul_right _
      _ = r ^ M * (1 - r)⁻¹ := by
        rw [tsum_geometric_of_lt_one hrpos hrlt]
        ring
  have hrM : r ^ M ≤ 1 / (a n : ℝ) := by
    rw [exp_neg_one_pow]
    exact one_div_le_one_div_of_le hA ha_expM
  have hgeomnonneg : 0 ≤ (1 - r)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr hrlt.le)
  rw [hsplit]
  calc
    (∑ k ∈ Finset.range M, ReciprocalTerm a (k + n)) +
        ∑' k : ℕ, ReciprocalTerm a (k + M + n) ≤
      (M : ℝ) / (a n : ℝ) + r ^ M * (1 - r)⁻¹ := add_le_add hhead htail
    _ ≤ (M : ℝ) / (a n : ℝ) +
        (1 / (a n : ℝ)) * (1 - r)⁻¹ := by
      gcongr
    _ = ((M : ℝ) + (1 - Real.exp (-1))⁻¹) / (a n : ℝ) := by
      simp only [r]
      ring

/-- The slowly growing factor occurring in the regularized tail estimate. -/
noncomputable def TailRegularizer (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (Nat.ceil (Real.log (a n : ℝ)) : ℝ) + (1 - Real.exp (-1))⁻¹

theorem tailRegularizer_pos (a : ℕ → ℕ) (n : ℕ) :
    0 < TailRegularizer a n := by
  rw [TailRegularizer]
  have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _)
    (inv_pos.mpr (sub_pos.mpr he))

/-- The regularized tail estimate gives
`D_n ≤ 2 F_n / a_n²`. -/
theorem differenceTail_le_two_regularizer_div_sq
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {N n : ℕ}
    (hExp : ∀ m ≥ N, Real.exp (m : ℝ) ≤ (a m : ℝ))
    (hn : N ≤ n) :
    DifferenceTail a n ≤
      2 * TailRegularizer a n / (a n : ℝ) ^ 2 := by
  have hA : (0 : ℝ) < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  have hA1 : (0 : ℝ) < (a n : ℝ) - 1 := by
    have hcast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
    linarith
  have hT : ReciprocalTail a n ≤ TailRegularizer a n / (a n : ℝ) := by
    exact reciprocalTail_le_ceilLog_add_geometric_div ha hamono hu hExp hn
  have hD := differenceTail_le_reciprocalTail_div ha hamono hu hv n
  have hF : 0 ≤ TailRegularizer a n := (tailRegularizer_pos a n).le
  calc
    DifferenceTail a n ≤ ReciprocalTail a n / ((a n : ℝ) - 1) := hD
    _ ≤ (TailRegularizer a n / (a n : ℝ)) / ((a n : ℝ) - 1) := by
      exact div_le_div_of_nonneg_right hT hA1.le
    _ ≤ 2 * TailRegularizer a n / (a n : ℝ) ^ 2 := by
      rw [div_div]
      rw [div_le_div_iff₀ (mul_pos hA hA1) (sq_pos_of_pos hA)]
      have hcast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
      have haineq : (a n : ℝ) ^ 2 ≤
          2 * ((a n : ℝ) * ((a n : ℝ) - 1)) := by
        nlinarith
      have hm := mul_le_mul_of_nonneg_left haineq hF
      nlinarith

/-- Consequently `H_n` is no smaller than `P_n a_n / sqrt(2F_n)`. -/
theorem prefix_mul_current_div_sqrt_regularizer_le_tailEnvelope
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {N n : ℕ}
    (hExp : ∀ m ≥ N, Real.exp (m : ℝ) ≤ (a m : ℝ))
    (hn : N ≤ n) :
    (PrefixProduct a n : ℝ) * (a n : ℝ) /
        Real.sqrt (2 * TailRegularizer a n) ≤ TailEnvelope a n := by
  have hA : (0 : ℝ) < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  have hP : (0 : ℝ) < (PrefixProduct a n : ℝ) := by
    exact_mod_cast prefixProduct_pos ha n
  have hD : 0 < DifferenceTail a n := differenceTail_pos ha hu hv n
  have hF : 0 < 2 * TailRegularizer a n :=
    mul_pos (by norm_num) (tailRegularizer_pos a n)
  have hDbound := differenceTail_le_two_regularizer_div_sq
    ha hamono hu hv hExp hn
  have hsquares :
      ((a n : ℝ) * Real.sqrt (DifferenceTail a n)) ^ 2 ≤
        (Real.sqrt (2 * TailRegularizer a n)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hD.le, Real.sq_sqrt hF.le]
    simpa [mul_comm] using (le_div_iff₀ (sq_pos_of_pos hA)).1 hDbound
  have hsqrt :
      (a n : ℝ) * Real.sqrt (DifferenceTail a n) ≤
        Real.sqrt (2 * TailRegularizer a n) :=
    (sq_le_sq₀ (mul_nonneg hA.le (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)).1 hsquares
  rw [TailEnvelope]
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hF) (Real.sqrt_pos.2 hD)]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hsqrt hP.le

/-- Quantitative comparison between the cumulative logarithm and the
envelope logarithm. -/
theorem cumulativeLog_sub_error_le_log_tailEnvelope
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {N n : ℕ}
    (hExp : ∀ m ≥ N, Real.exp (m : ℝ) ≤ (a m : ℝ))
    (hn : N ≤ n) :
    CumulativeLog a n - Real.log (2 * TailRegularizer a n) / 2 ≤
      Real.log (TailEnvelope a n) := by
  have hA : (0 : ℝ) < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  have hP : (0 : ℝ) < (PrefixProduct a n : ℝ) := by
    exact_mod_cast prefixProduct_pos ha n
  have hF : 0 < 2 * TailRegularizer a n :=
    mul_pos (by norm_num) (tailRegularizer_pos a n)
  have hlower := prefix_mul_current_div_sqrt_regularizer_le_tailEnvelope
    ha hamono hu hv hExp hn
  have hlowerpos : 0 <
      (PrefixProduct a n : ℝ) * (a n : ℝ) /
        Real.sqrt (2 * TailRegularizer a n) :=
    div_pos (mul_pos hP hA) (Real.sqrt_pos.2 hF)
  have hlog := Real.log_le_log hlowerpos hlower
  have hid : Real.log
      ((PrefixProduct a n : ℝ) * (a n : ℝ) /
        Real.sqrt (2 * TailRegularizer a n)) =
      CumulativeLog a n - Real.log (2 * TailRegularizer a n) / 2 := by
    rw [Real.log_div (mul_ne_zero hP.ne' hA.ne') (Real.sqrt_pos.2 hF).ne']
    rw [Real.log_mul hP.ne' hA.ne', Real.log_sqrt hF.le]
    rw [log_prefixProduct ha n]
    simp [CumulativeLog, Finset.sum_range_succ]
  rwa [hid] at hlog

/-- If `log a_{j+N}` is `O(2^j)`, the logarithm of the regularizing factor is
`o(2^j)`. -/
theorem log_tailRegularizer_div_two_pow_tendsto_zero_of_bound
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    {N : ℕ} {U : ℝ} (hU : 0 < U)
    (hbound : ∀ᶠ j in atTop,
      Real.log (a (j + N) : ℝ) ≤ U * (2 : ℝ) ^ j) :
    Tendsto
      (fun j : ℕ ↦ Real.log (2 * TailRegularizer a (j + N)) /
        (2 : ℝ) ^ j) atTop (𝓝 0) := by
  let G : ℝ := (1 - Real.exp (-1))⁻¹
  let C : ℝ := 2 * (U + 1 + G)
  have her : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have herpos : 0 < Real.exp (-1) := Real.exp_pos _
  have hdenpos : 0 < 1 - Real.exp (-1) := sub_pos.mpr her
  have hdenle : 1 - Real.exp (-1) ≤ 1 := by linarith
  have hGone : 1 ≤ G := by
    dsimp [G]
    exact (one_le_inv₀ hdenpos).2 hdenle
  have hC : 0 < C := by
    dsimp [C]
    linarith
  have hpowlim : Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hconstlim :
      Tendsto (fun j : ℕ ↦ Real.log C / (2 : ℝ) ^ j) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpowlim
  have hlinear := tendsto_pow_const_div_const_pow_of_one_lt 1
    (show (1 : ℝ) < 2 by norm_num)
  have hupperlim : Tendsto
      (fun j : ℕ ↦ (Real.log C + (j : ℝ) * Real.log 2) / (2 : ℝ) ^ j)
      atTop (𝓝 0) := by
    have hadd := hconstlim.add (hlinear.const_mul (Real.log 2))
    convert hadd using 1
    · funext j
      field_simp
    · simp
  apply squeeze_zero'
  · exact Eventually.of_forall fun j ↦ by
      have hFone : 1 ≤ 2 * TailRegularizer a (j + N) := by
        have hM : (0 : ℝ) ≤
            (Nat.ceil (Real.log (a (j + N) : ℝ)) : ℝ) := Nat.cast_nonneg _
        rw [TailRegularizer]
        change 1 ≤ 2 * (_ + G)
        nlinarith
      exact div_nonneg (Real.log_nonneg hFone) (by positivity)
  · filter_upwards [hbound] with j hj
    have hlog0 : 0 ≤ Real.log (a (j + N) : ℝ) := by
      apply Real.log_nonneg
      have hcast : (2 : ℝ) ≤ (a (j + N) : ℝ) := by exact_mod_cast ha (j + N)
      linarith
    have hceil :
        (Nat.ceil (Real.log (a (j + N) : ℝ)) : ℝ) ≤
          Real.log (a (j + N) : ℝ) + 1 :=
      (Nat.ceil_lt_add_one hlog0).le
    have hpone : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hfactor : 2 * TailRegularizer a (j + N) ≤ C * (2 : ℝ) ^ j := by
      rw [TailRegularizer]
      change 2 * (_ + G) ≤ C * (2 : ℝ) ^ j
      dsimp [C]
      nlinarith
    have hleftpos : 0 < 2 * TailRegularizer a (j + N) :=
      mul_pos (by norm_num) (tailRegularizer_pos _ _)
    have hrightpos : 0 < C * (2 : ℝ) ^ j := mul_pos hC (by positivity)
    have hlogle : Real.log (2 * TailRegularizer a (j + N)) ≤
        Real.log C + (j : ℝ) * Real.log 2 := by
      have hh := (Real.log_le_log_iff hleftpos hrightpos).2 hfactor
      rw [Real.log_mul hC.ne' (pow_pos (by norm_num) j).ne', Real.log_pow] at hh
      simpa [Nat.cast_ofNat] using hh
    exact div_le_div_of_nonneg_right hlogle (by positivity)
  · exact hupperlim

/-- A finite shifted envelope limit supplies the `O(2^j)` bound on the
current logarithm required by the preceding lemma. -/
theorem shifted_log_current_eventually_le_two_pow
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {N : ℕ} {ell : ℝ}
    (hlim : Tendsto
      (BinaryLogRatio (fun j ↦ TailEnvelope a (j + N))) atTop (𝓝 ell)) :
    ∃ U : ℝ, 0 < U ∧ ∀ᶠ j in atTop,
      Real.log (a (j + N) : ℝ) ≤ U * (2 : ℝ) ^ j := by
  let U0 : ℝ := |ell| + 1
  let U : ℝ := 2 * U0
  have hU0 : 0 < U0 := by dsimp [U0]; positivity
  have hellU : ell < U0 := by
    dsimp [U0]
    linarith [le_abs_self ell]
  have hratio : ∀ᶠ r in atTop,
      BinaryLogRatio (fun j ↦ TailEnvelope a (j + N)) r < U0 :=
    (tendsto_order.1 hlim).2 _ hellU
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hratio
  obtain ⟨Jt, hJt⟩ := eventually_atTop.1
    (eventually_reciprocalTail_le_one a)
  refine ⟨U, mul_pos (by norm_num) hU0, ?_⟩
  filter_upwards [eventually_ge_atTop (max J Jt)] with j hj
  let m : ℕ := j + N
  have hJj : J ≤ j := (le_max_left J Jt).trans hj
  have hratioSucc := hJ (j + 1) (by omega)
  have hp : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  have hlogH : Real.log (TailEnvelope a (m + 1)) <
      U0 * (2 : ℝ) ^ (j + 1) := by
    change Real.log (TailEnvelope a ((j + 1) + N)) /
      (2 : ℝ) ^ (j + 1) < U0 at hratioSucc
    have := (div_lt_iff₀ hp).1 hratioSucc
    simpa [m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  have htail : ReciprocalTail a (m + 1) ≤ 1 := by
    apply hJt (m + 1)
    have : Jt ≤ j := le_trans (le_max_right _ _) hj
    dsimp [m]
    omega
  have hamH : (a m : ℝ) ≤ TailEnvelope a (m + 1) :=
    current_le_tailEnvelope_succ_of_tail_le_one ha hamono hu hv htail
  have haPos : (0 : ℝ) < (a m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha m))
  have hlogA : Real.log (a m : ℝ) ≤ Real.log (TailEnvelope a (m + 1)) :=
    Real.log_le_log haPos hamH
  calc
    Real.log (a (j + N) : ℝ) ≤ Real.log (TailEnvelope a (m + 1)) := by
      simpa [m] using hlogA
    _ ≤ U0 * (2 : ℝ) ^ (j + 1) := hlogH.le
    _ = U * (2 : ℝ) ^ j := by
      rw [pow_succ]
      simp [U]
      ring

/-- In the positive-limit branch, the cumulative logarithms have the same
normalized limit as the tail envelope. -/
theorem positive_shifted_envelope_limit_cumulativeLog
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {N : ℕ} {ell : ℝ} (hell : 0 < ell)
    (hlim : Tendsto
      (BinaryLogRatio (fun j ↦ TailEnvelope a (j + N))) atTop (𝓝 ell)) :
    Tendsto
      (fun j : ℕ ↦ CumulativeLog a (j + N) / (2 : ℝ) ^ j)
      atTop (𝓝 ell) := by
  have hExpEvent := positive_shifted_envelope_limit_forces_exp_growth
    ha hamono hu hv hell hlim
  obtain ⟨Ne, hNe⟩ := eventually_atTop.1 hExpEvent
  obtain ⟨U, hU, hbound⟩ :=
    shifted_log_current_eventually_le_two_pow ha hamono hu hv hlim
  have herr := log_tailRegularizer_div_two_pow_tendsto_zero_of_bound ha hU hbound
  have herrHalf : Tendsto
      (fun j : ℕ ↦ Real.log (2 * TailRegularizer a (j + N)) /
        (2 * (2 : ℝ) ^ j)) atTop (𝓝 0) := by
    have hh := herr.const_mul (1 / 2 : ℝ)
    convert hh using 1
    · funext j
      field_simp
    · simp
  have hupperlim : Tendsto
      (fun j : ℕ ↦
        BinaryLogRatio (fun r ↦ TailEnvelope a (r + N)) j +
          Real.log (2 * TailRegularizer a (j + N)) / (2 * (2 : ℝ) ^ j))
      atTop (𝓝 ell) := by
    simpa using hlim.add herrHalf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim hupperlim
  · exact Eventually.of_forall fun j ↦ by
      have hlog := log_tailEnvelope_le_cumulativeLog ha hu hv (j + N)
      have hp : 0 ≤ (2 : ℝ) ^ j := by positivity
      change Real.log (TailEnvelope a (j + N)) / (2 : ℝ) ^ j ≤
        CumulativeLog a (j + N) / (2 : ℝ) ^ j
      exact div_le_div_of_nonneg_right hlog hp
  · filter_upwards [eventually_ge_atTop Ne] with j hj
    have hNj : Ne ≤ j + N := by omega
    have hclose := cumulativeLog_sub_error_le_log_tailEnvelope
      ha hamono hu hv hNe hNj
    have hrearrange : CumulativeLog a (j + N) ≤
        Real.log (TailEnvelope a (j + N)) +
          Real.log (2 * TailRegularizer a (j + N)) / 2 := by
      linarith
    have hp : 0 ≤ (2 : ℝ) ^ j := by positivity
    have hdiv := div_le_div_of_nonneg_right hrearrange hp
    change CumulativeLog a (j + N) / (2 : ℝ) ^ j ≤
      Real.log (TailEnvelope a (j + N)) / (2 : ℝ) ^ j +
        Real.log (2 * TailRegularizer a (j + N)) / (2 * (2 : ℝ) ^ j)
    calc
      CumulativeLog a (j + N) / (2 : ℝ) ^ j ≤
          (Real.log (TailEnvelope a (j + N)) +
            Real.log (2 * TailRegularizer a (j + N)) / 2) /
              (2 : ℝ) ^ j := hdiv
      _ = _ := by field_simp

/-- Taking first differences of `B_n` gives the regularized limit for the
individual logarithms. -/
theorem positive_shifted_envelope_limit_log_current
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {N : ℕ} {ell : ℝ} (hell : 0 < ell)
    (hlim : Tendsto
      (BinaryLogRatio (fun j ↦ TailEnvelope a (j + N))) atTop (𝓝 ell)) :
    Tendsto
      (BinaryLogRatio (fun j ↦ (a (j + N) : ℝ))) atTop (𝓝 (ell / 2)) := by
  let B : ℕ → ℝ := fun j ↦ CumulativeLog a (j + N) / (2 : ℝ) ^ j
  have hB : Tendsto B atTop (𝓝 ell) :=
    positive_shifted_envelope_limit_cumulativeLog ha hamono hu hv hell hlim
  have hBsucc : Tendsto (fun j : ℕ ↦ B (j + 1)) atTop (𝓝 ell) :=
    hB.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun j : ℕ ↦ B (j + 1) - B j / 2)
      atTop (𝓝 (ell / 2)) := by
    convert hBsucc.sub (hB.div_const 2) using 1
    simp
    ring
  have hshifted : Tendsto
      (fun j : ℕ ↦ BinaryLogRatio (fun r ↦ (a (r + N) : ℝ)) (j + 1))
      atTop (𝓝 (ell / 2)) := by
    convert hdiff using 1
    funext j
    rw [BinaryLogRatio]
    dsimp [B]
    rw [CumulativeLog, CumulativeLog, Finset.sum_range_succ]
    rw [pow_succ]
    field_simp
    ring_nf
  exact (tendsto_add_atTop_iff_nat 1).1 hshifted

/-- A positive sequence whose logarithm has a negative binary-normalized
limit converges to zero. -/
theorem tendsto_zero_of_normalized_log_tendsto_neg
    {X : ℕ → ℝ} (hX : ∀ n, 0 < X n)
    {L : ℝ} (hL : L < 0)
    (hlim : Tendsto (fun n : ℕ ↦ Real.log (X n) / (2 : ℝ) ^ n)
      atTop (𝓝 L)) :
    Tendsto X atTop (𝓝 0) := by
  have hhalf : L < L / 2 := by linarith
  have hratio : ∀ᶠ n in atTop,
      Real.log (X n) / (2 : ℝ) ^ n < L / 2 :=
    (tendsto_order.1 hlim).2 _ hhalf
  have hpow : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have harg : Tendsto (fun n : ℕ ↦ (L / 2) * (2 : ℝ) ^ n) atTop atBot :=
    hpow.const_mul_atTop_of_neg (by linarith)
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp ((L / 2) * (2 : ℝ) ^ n))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp harg
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ (hX n).le
  · filter_upwards [hratio] with n hn
    have hp : 0 < (2 : ℝ) ^ n := by positivity
    have hlog : Real.log (X n) < (L / 2) * (2 : ℝ) ^ n :=
      (div_lt_iff₀ hp).1 hn
    calc
      X n = Real.exp (Real.log (X n)) := (Real.exp_log (hX n)).symm
      _ ≤ Real.exp ((L / 2) * (2 : ℝ) ^ n) :=
        Real.exp_le_exp.mpr hlog.le
  · exact hexp

end Erdos265

/-!
# The second residual

We study `E_n = T_n / (1 - T_n) - V_n`.  Its strict positivity gives the
second rational gap, while its analytic upper bound contains the decisive
product `T_n T_{n+1}`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos265

noncomputable def SecondResidual (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ReciprocalTail a n / (1 - ReciprocalTail a n) -
    ShiftedReciprocalTail a n

theorem reciprocalTail_eq_add_succ
    {a : ℕ → ℕ} (hu : Summable (ReciprocalTerm a)) (n : ℕ) :
    ReciprocalTail a n = ReciprocalTerm a n + ReciprocalTail a (n + 1) :=
  seriesTail_eq_add_succ hu n

theorem shiftedReciprocalTail_eq_add_succ
    {a : ℕ → ℕ} (hv : Summable (ShiftedReciprocalTerm a)) (n : ℕ) :
    ShiftedReciprocalTail a n =
      ShiftedReciprocalTerm a n + ShiftedReciprocalTail a (n + 1) :=
  seriesTail_eq_add_succ hv n

theorem reciprocalTail_pos
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a)) (n : ℕ) :
    0 < ReciprocalTail a n := by
  rw [reciprocalTail_eq_add_succ hu n]
  have hhead : 0 < ReciprocalTerm a n := by
    have hcast : (0 : ℝ) < (a n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
    rw [ReciprocalTerm]
    exact one_div_pos.mpr hcast
  exact add_pos_of_pos_of_nonneg hhead (reciprocalTail_nonneg ha (n + 1))

theorem reciprocalTerm_le_shiftedReciprocalTerm
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    ReciprocalTerm a n ≤ ShiftedReciprocalTerm a n := by
  have hA1 : (0 : ℝ) < (a n : ℝ) - 1 := by
    have hcast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
    linarith
  rw [ReciprocalTerm, ShiftedReciprocalTerm]
  exact one_div_le_one_div_of_le hA1 (by linarith)

theorem reciprocalTail_le_shiftedReciprocalTail
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a)) (n : ℕ) :
    ReciprocalTail a n ≤ ShiftedReciprocalTail a n := by
  exact (summable_seriesTail hu n).tsum_le_tsum
    (fun k ↦ reciprocalTerm_le_shiftedReciprocalTerm ha (k + n))
    (summable_seriesTail hv n)

theorem shiftedReciprocalTerm_eq_fraction
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    ShiftedReciprocalTerm a n =
      ReciprocalTerm a n / (1 - ReciprocalTerm a n) := by
  have hA : (0 : ℝ) < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  have hA1 : (0 : ℝ) < (a n : ℝ) - 1 := by
    have hcast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
    linarith
  rw [ShiftedReciprocalTerm, ReciprocalTerm]
  field_simp

private theorem shiftedTerm_le_outerFraction
    {A T : ℝ} (hA : 1 < A) (hT : T < 1) (huT : 1 / A ≤ T) :
    1 / (A - 1) ≤ (1 / A) / (1 - T) := by
  have hden1 : 0 < A - 1 := sub_pos.mpr hA
  have hdenT : 0 < A * (1 - T) :=
    mul_pos (lt_trans zero_lt_one hA) (sub_pos.mpr hT)
  have hdenle : A * (1 - T) ≤ A - 1 := by
    have hm := mul_le_mul_of_nonneg_left huT (le_of_lt (lt_trans zero_lt_one hA))
    field_simp at hm
    nlinarith
  calc
    1 / (A - 1) ≤ 1 / (A * (1 - T)) :=
      one_div_le_one_div_of_le hdenT hdenle
    _ = (1 / A) / (1 - T) := by field_simp

private theorem shiftedTerm_lt_outerFraction
    {A T : ℝ} (hA : 1 < A) (hT : T < 1) (huT : 1 / A < T) :
    1 / (A - 1) < (1 / A) / (1 - T) := by
  have hden1 : 0 < A - 1 := sub_pos.mpr hA
  have hdenT : 0 < A * (1 - T) :=
    mul_pos (lt_trans zero_lt_one hA) (sub_pos.mpr hT)
  have hdenlt : A * (1 - T) < A - 1 := by
    have hm := mul_lt_mul_of_pos_left huT (lt_trans zero_lt_one hA)
    field_simp at hm
    nlinarith
  calc
    1 / (A - 1) < 1 / (A * (1 - T)) :=
      one_div_lt_one_div_of_lt hdenT hdenlt
    _ = (1 / A) / (1 - T) := by field_simp

/-- Strict positivity of the second residual whenever `T_n < 1`. -/
theorem secondResidual_pos
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {n : ℕ} (hTlt : ReciprocalTail a n < 1) :
    0 < SecondResidual a n := by
  let T := ReciprocalTail a n
  let x := ReciprocalTerm a n
  let y := ReciprocalTail a (n + 1)
  have hdecomp : T = x + y := reciprocalTail_eq_add_succ hu n
  have hy : 0 < y := reciprocalTail_pos ha hu (n + 1)
  have hxT : x < T := by linarith
  have hA : (1 : ℝ) < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  have hhead : ShiftedReciprocalTerm a n < x / (1 - T) := by
    change 1 / ((a n : ℝ) - 1) < (1 / (a n : ℝ)) / (1 - T)
    exact shiftedTerm_lt_outerFraction hA hTlt hxT
  have hrestTerm : ∀ k : ℕ,
      ShiftedReciprocalTerm a (k + (n + 1)) ≤
        ReciprocalTerm a (k + (n + 1)) / (1 - T) := by
    intro k
    let i := k + (n + 1)
    have hni : n ≤ i := by dsimp [i]; omega
    have hmono : (a n : ℝ) ≤ (a i : ℝ) := by exact_mod_cast hamono hni
    have hAi : (1 : ℝ) < (a i : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega) (ha i))
    have hui : 1 / (a i : ℝ) ≤ T := by
      have hxn : 1 / (a i : ℝ) ≤ 1 / (a n : ℝ) :=
        one_div_le_one_div_of_le (lt_trans zero_lt_one hA) hmono
      simpa [x, ReciprocalTerm] using hxn.trans hxT.le
    rw [ShiftedReciprocalTerm, ReciprocalTerm]
    exact shiftedTerm_le_outerFraction hAi hTlt hui
  have hden : 0 < 1 - T := sub_pos.mpr hTlt
  have hrest : ShiftedReciprocalTail a (n + 1) ≤ y / (1 - T) := by
    have hsum := (summable_seriesTail hv (n + 1)).tsum_le_tsum hrestTerm
      ((summable_seriesTail hu (n + 1)).div_const (1 - T))
    calc
      ShiftedReciprocalTail a (n + 1) ≤
          ∑' k : ℕ, ReciprocalTerm a (k + (n + 1)) / (1 - T) := by
        simpa [ShiftedReciprocalTail, SeriesTail] using hsum
      _ = y / (1 - T) := by
        rw [tsum_div_const]
        simp [y, ReciprocalTail, SeriesTail]
  have hV : ShiftedReciprocalTail a n < T / (1 - T) := by
    rw [shiftedReciprocalTail_eq_add_succ hv n]
    calc
      ShiftedReciprocalTerm a n + ShiftedReciprocalTail a (n + 1) <
          x / (1 - T) + y / (1 - T) := add_lt_add_of_lt_of_le hhead hrest
      _ = T / (1 - T) := by rw [hdecomp]; ring
  rw [SecondResidual]
  change 0 < T / (1 - T) - ShiftedReciprocalTail a n
  linarith

private theorem algebraic_residual_upper
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1 / 2) :
    (x + y) / (1 - (x + y)) - x / (1 - x) - y ≤
      8 * (x + y) * y := by
  let t := x + y
  let d := (1 - t) * (1 - x)
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have hxt : x ≤ t := by dsimp [t]; linarith
  have ht : t ≤ 1 / 2 := hxy
  have h1t : 0 < 1 - t := by linarith
  have h1x : 0 < 1 - x := by linarith
  have hdpos : 0 < d := mul_pos h1t h1x
  have hid : t / (1 - t) - x / (1 - x) - y =
      y * (t + x - t * x) / d := by
    have hxyden : 1 - (x + y) ≠ 0 := by
      dsimp [t] at h1t
      linarith
    have hxden : 1 - x ≠ 0 := h1x.ne'
    dsimp [t, d]
    field_simp [hxyden, hxden]
    ring
  rw [show x + y = t by rfl, hid]
  rw [div_le_iff₀ hdpos]
  have hcore : t + x - t * x ≤ 2 * t := by
    have htx : 0 ≤ t * x := mul_nonneg ht0 hx
    linarith
  have hnum : y * (t + x - t * x) ≤ 2 * t * y := by
    nlinarith
  have hd : (1 : ℝ) / 4 ≤ d := by
    have ha : (1 : ℝ) / 2 ≤ 1 - t := by linarith
    have hb : (1 : ℝ) / 2 ≤ 1 - x := by linarith
    have hm := mul_le_mul ha hb (by norm_num) (by linarith)
    norm_num at hm ⊢
    exact hm
  have hright : 2 * t * y ≤ 8 * t * y * d := by
    have hty : 0 ≤ 8 * t * y := by positivity
    have hm := mul_le_mul_of_nonneg_left hd hty
    nlinarith
  exact hnum.trans hright

/-- For `T_n ≤ 1/2`, the residual is at most `8 T_n T_{n+1}`. -/
theorem secondResidual_le_eight_mul_tails
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {n : ℕ} (hT : ReciprocalTail a n ≤ 1 / 2) :
    SecondResidual a n ≤
      8 * ReciprocalTail a n * ReciprocalTail a (n + 1) := by
  let T := ReciprocalTail a n
  let x := ReciprocalTerm a n
  let y := ReciprocalTail a (n + 1)
  have hdecomp : T = x + y := reciprocalTail_eq_add_succ hu n
  have hx : 0 ≤ x := reciprocalTerm_nonneg ha n
  have hy : 0 ≤ y := reciprocalTail_nonneg ha (n + 1)
  have hVlower : x / (1 - x) + y ≤ ShiftedReciprocalTail a n := by
    rw [shiftedReciprocalTail_eq_add_succ hv n]
    rw [← shiftedReciprocalTerm_eq_fraction ha n]
    exact add_le_add le_rfl
      (reciprocalTail_le_shiftedReciprocalTail ha hu hv (n + 1))
  have halg := algebraic_residual_upper hx hy (by simpa [T, hdecomp] using hT)
  rw [SecondResidual]
  change T / (1 - T) - ShiftedReciprocalTail a n ≤ 8 * T * y
  calc
    T / (1 - T) - ShiftedReciprocalTail a n ≤
        T / (1 - T) - (x / (1 - x) + y) := sub_le_sub_left hVlower _
    _ = T / (1 - T) - x / (1 - x) - y := by ring
    _ ≤ 8 * T * y := by simpa [hdecomp] using halg

/-! ## Rational denominator lower bound -/

noncomputable def ScaledReciprocalTail
    (b : ℤ) (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((b * PrefixProduct a n : ℤ) : ℝ) * ReciprocalTail a n

noncomputable def ScaledShiftedReciprocalTail
    (d : ℤ) (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((d * ShiftedPrefixProduct a n : ℤ) : ℝ) * ShiftedReciprocalTail a n

theorem scaledReciprocalTail_isInteger
    {a : ℕ → ℕ} {b : ℤ}
    (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    (hzero : ∃ r : ℤ, ScaledReciprocalTail b a 0 = (r : ℝ)) :
    ∀ n, ∃ r : ℤ, ScaledReciprocalTail b a n = (r : ℝ) := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      obtain ⟨r, hr⟩ := ih
      let A : ℝ := a n
      let B : ℝ := (b * PrefixProduct a n : ℤ)
      have hA : 0 < A := by
        dsimp [A]
        exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
      have hrec : A * ReciprocalTail a n =
          1 + A * ReciprocalTail a (n + 1) := by
        rw [reciprocalTail_eq_add_succ hu n, ReciprocalTerm]
        change A * (1 / A + ReciprocalTail a (n + 1)) = _
        field_simp
      have hr' : B * ReciprocalTail a n = (r : ℝ) := by
        simpa [ScaledReciprocalTail, B] using hr
      refine ⟨(a n : ℤ) * r - b * PrefixProduct a n, ?_⟩
      rw [ScaledReciprocalTail, prefixProduct_succ]
      calc
        (((b * (PrefixProduct a n * (a n : ℤ)) : ℤ) : ℝ) *
            ReciprocalTail a (n + 1)) =
            (B * A) * ReciprocalTail a (n + 1) := by
          simp only [A, B]
          push_cast
          ring
        _ = A * (B * ReciprocalTail a (n + 1)) := by ring
        _ = A * (B * ReciprocalTail a n - B / A) := by
          have : B * ReciprocalTail a (n + 1) =
              B * ReciprocalTail a n - B / A := by
            apply (eq_sub_iff_add_eq).2
            calc
              B * ReciprocalTail a (n + 1) + B / A =
                  (B / A) * (A * ReciprocalTail a (n + 1) + 1) := by
                field_simp
              _ = (B / A) * (A * ReciprocalTail a n) := by rw [hrec]; ring
              _ = B * ReciprocalTail a n := by field_simp
          rw [this]
        _ = A * (r : ℝ) - B := by rw [hr']; field_simp
        _ = (((a n : ℤ) * r - b * PrefixProduct a n : ℤ) : ℝ) := by
          simp only [A, B]
          push_cast
          ring

theorem scaledShiftedReciprocalTail_isInteger
    {a : ℕ → ℕ} {d : ℤ}
    (ha : ∀ n, 2 ≤ a n)
    (hv : Summable (ShiftedReciprocalTerm a))
    (hzero : ∃ s : ℤ, ScaledShiftedReciprocalTail d a 0 = (s : ℝ)) :
    ∀ n, ∃ s : ℤ, ScaledShiftedReciprocalTail d a n = (s : ℝ) := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      obtain ⟨s, hs⟩ := ih
      let A : ℝ := (a n : ℝ) - 1
      let B : ℝ := (d * ShiftedPrefixProduct a n : ℤ)
      have hA : 0 < A := by
        have hcast : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha n
        dsimp [A]
        linarith
      have hrec : A * ShiftedReciprocalTail a n =
          1 + A * ShiftedReciprocalTail a (n + 1) := by
        rw [shiftedReciprocalTail_eq_add_succ hv n, ShiftedReciprocalTerm]
        change A * (1 / A + ShiftedReciprocalTail a (n + 1)) = _
        field_simp
      have hs' : B * ShiftedReciprocalTail a n = (s : ℝ) := by
        simpa [ScaledShiftedReciprocalTail, B] using hs
      refine ⟨((a n : ℤ) - 1) * s - d * ShiftedPrefixProduct a n, ?_⟩
      rw [ScaledShiftedReciprocalTail, shiftedPrefixProduct_succ]
      calc
        (((d * (ShiftedPrefixProduct a n * ((a n : ℤ) - 1)) : ℤ) : ℝ) *
            ShiftedReciprocalTail a (n + 1)) =
            (B * A) * ShiftedReciprocalTail a (n + 1) := by
          simp only [A, B]
          push_cast
          ring
        _ = A * (B * ShiftedReciprocalTail a (n + 1)) := by ring
        _ = A * (B * ShiftedReciprocalTail a n - B / A) := by
          have : B * ShiftedReciprocalTail a (n + 1) =
              B * ShiftedReciprocalTail a n - B / A := by
            apply (eq_sub_iff_add_eq).2
            calc
              B * ShiftedReciprocalTail a (n + 1) + B / A =
                  (B / A) * (A * ShiftedReciprocalTail a (n + 1) + 1) := by
                field_simp
              _ = (B / A) * (A * ShiftedReciprocalTail a n) := by rw [hrec]; ring
              _ = B * ShiftedReciprocalTail a n := by field_simp
          rw [this]
        _ = A * (s : ℝ) - B := by rw [hs']; field_simp
        _ = ((((a n : ℤ) - 1) * s -
            d * ShiftedPrefixProduct a n : ℤ) : ℝ) := by
          simp only [A, B]
          push_cast
          ring

theorem exists_integral_scales_for_two_tails
    {a : ℕ → ℕ} (ha : IsRationalPairSequence a) :
    ∃ b d : ℤ, 0 < b ∧ 0 < d ∧
      (∀ n, ∃ r : ℤ, ScaledReciprocalTail b a n = (r : ℝ)) ∧
      (∀ n, ∃ s : ℤ, ScaledShiftedReciprocalTail d a n = (s : ℝ)) := by
  obtain ⟨qu, hqu⟩ := ha.2.2.2.2.1
  obtain ⟨qv, hqv⟩ := ha.2.2.2.2.2
  let b : ℤ := qu.den
  let d : ℤ := qv.den
  have hb : 0 < b := by dsimp [b]; exact_mod_cast qu.den_pos
  have hd : 0 < d := by dsimp [d]; exact_mod_cast qv.den_pos
  have hu := summable_reciprocalTerm_of_admissible ha
  have hv := summable_shiftedReciprocalTerm_of_admissible ha
  have hT0 : ReciprocalTail a 0 = (qu : ℝ) := by
    simpa [ReciprocalTail, SeriesTail, ReciprocalTerm] using hqu
  have hV0 : ShiftedReciprocalTail a 0 = (qv : ℝ) := by
    simpa [ShiftedReciprocalTail, SeriesTail, ShiftedReciprocalTerm] using hqv
  have hTb : ∃ r : ℤ, ScaledReciprocalTail b a 0 = (r : ℝ) := by
    refine ⟨qu.num, ?_⟩
    simp only [ScaledReciprocalTail, prefixProduct_zero, mul_one]
    rw [hT0]
    simpa [b] using rat_den_mul_cast qu
  have hVd : ∃ s : ℤ, ScaledShiftedReciprocalTail d a 0 = (s : ℝ) := by
    refine ⟨qv.num, ?_⟩
    simp only [ScaledShiftedReciprocalTail, shiftedPrefixProduct_zero, mul_one]
    rw [hV0]
    simpa [d] using rat_den_mul_cast qv
  exact ⟨b, d, hb, hd,
    scaledReciprocalTail_isInteger
      (two_le_of_isRationalPairSequence ha) hu hTb,
    scaledShiftedReciprocalTail_isInteger
      (two_le_of_isRationalPairSequence ha) hv hVd⟩

/-- Combining the two integral tail representations makes the positive
residual an integer divided by a denominator no larger than `bd P_n²`. -/
theorem one_le_scales_mul_prefix_sq_mul_secondResidual
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n)
    (hu : Summable (ReciprocalTerm a))
    {b d : ℤ} (hb : 0 < b) (hd : 0 < d)
    (hintT : ∀ n, ∃ r : ℤ, ScaledReciprocalTail b a n = (r : ℝ))
    (hintV : ∀ n, ∃ s : ℤ, ScaledShiftedReciprocalTail d a n = (s : ℝ))
    {n : ℕ} (hTlt : ReciprocalTail a n < 1)
    (hE : 0 < SecondResidual a n) :
    1 ≤ ((b * d : ℤ) : ℝ) * (PrefixProduct a n : ℝ) ^ 2 *
      SecondResidual a n := by
  obtain ⟨r, hr⟩ := hintT n
  obtain ⟨s, hs⟩ := hintV n
  let B : ℤ := b * PrefixProduct a n
  let D : ℤ := d * ShiftedPrefixProduct a n
  let T : ℝ := ReciprocalTail a n
  let V : ℝ := ShiftedReciprocalTail a n
  let E : ℝ := SecondResidual a n
  have hB : 0 < B := mul_pos hb (prefixProduct_pos ha n)
  have hD : 0 < D := mul_pos hd (shiftedPrefixProduct_pos ha n)
  have hBr : (B : ℝ) * T = (r : ℝ) := by
    simpa [ScaledReciprocalTail, B, T] using hr
  have hDs : (D : ℝ) * V = (s : ℝ) := by
    simpa [ScaledShiftedReciprocalTail, D, V] using hs
  have hTpos : 0 < T := reciprocalTail_pos ha hu n
  have hrpos : 0 < r := by
    exact_mod_cast (show (0 : ℝ) < (r : ℝ) by
      rw [← hBr]
      exact mul_pos (by exact_mod_cast hB) hTpos)
  have hrB : r < B := by
    exact_mod_cast (show (r : ℝ) < (B : ℝ) by
      rw [← hBr]
      have hBreal : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
      nlinarith)
  have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hBrne : ((B - r : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr hrB.ne')
  have hsubne : (B : ℝ) - (r : ℝ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr hrB.ne')
  have hTform : T = (r : ℝ) / (B : ℝ) := by
    exact (eq_div_iff hBne).2 (by simpa [mul_comm] using hBr)
  have hVform : V = (s : ℝ) / (D : ℝ) := by
    exact (eq_div_iff hDne).2 (by simpa [mul_comm] using hDs)
  have hscaledInt :
      (((D * (B - r) : ℤ) : ℝ) * E) =
        ((D * r - s * (B - r) : ℤ) : ℝ) := by
    change ((D * (B - r) : ℤ) : ℝ) * SecondResidual a n = _
    rw [SecondResidual]
    change ((D * (B - r) : ℤ) : ℝ) * (T / (1 - T) - V) = _
    rw [hTform, hVform]
    push_cast
    rw [show ((r : ℝ) / (B : ℝ)) / (1 - (r : ℝ) / (B : ℝ)) =
      (r : ℝ) / ((B : ℝ) - (r : ℝ)) by
        field_simp [hBne, hsubne]]
    field_simp [hDne, hsubne]
  have hden : 0 < D * (B - r) :=
    mul_pos hD (sub_pos.mpr hrB)
  have hnum : 0 < D * r - s * (B - r) := by
    exact_mod_cast (show (0 : ℝ) <
        ((D * r - s * (B - r) : ℤ) : ℝ) by
      rw [← hscaledInt]
      exact mul_pos (by exact_mod_cast hden) hE)
  have hnumOne : (1 : ℤ) ≤ D * r - s * (B - r) := by omega
  have honeScaled : 1 ≤ ((D * (B - r) : ℤ) : ℝ) * E := by
    rw [hscaledInt]
    exact_mod_cast hnumOne
  have hden_le : D * (B - r) ≤ D * B := by
    have : B - r ≤ B := by omega
    exact mul_le_mul_of_nonneg_left this hD.le
  have honeDB : 1 ≤ ((D * B : ℤ) : ℝ) * E := by
    calc
      1 ≤ ((D * (B - r) : ℤ) : ℝ) * E := honeScaled
      _ ≤ ((D * B : ℤ) : ℝ) * E := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hden_le) hE.le
  have hQle : ShiftedPrefixProduct a n ≤ PrefixProduct a n :=
    shiftedPrefixProduct_le_prefixProduct ha n
  have hscale_le : D * B ≤ (b * d) * PrefixProduct a n ^ 2 := by
    dsimp [B, D]
    have hbd : 0 ≤ b * d := (mul_pos hb hd).le
    have hm := mul_le_mul_of_nonneg_left hQle hbd
    nlinarith [prefixProduct_pos ha n]
  calc
    1 ≤ ((D * B : ℤ) : ℝ) * E := honeDB
    _ ≤ (((b * d) * PrefixProduct a n ^ 2 : ℤ) : ℝ) * E := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hscale_le) hE.le
    _ = ((b * d : ℤ) : ℝ) * (PrefixProduct a n : ℝ) ^ 2 *
        SecondResidual a n := by
      change (((b * d) * PrefixProduct a n ^ 2 : ℤ) : ℝ) *
        SecondResidual a n = _
      push_cast
      ring

/-- A positive expression dominating `P_n² E_n` in the regularized-growth
branch.  It is written using `2F_n` so that the existing logarithmic error
lemma applies directly. -/
noncomputable def ResidualMajorant (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  2 * (PrefixProduct a n : ℝ) ^ 2 *
      (2 * TailRegularizer a n) * (2 * TailRegularizer a (n + 1)) /
    ((a n : ℝ) * (a (n + 1) : ℝ))

theorem prefix_sq_mul_secondResidual_le_majorant
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {N n : ℕ}
    (hExp : ∀ m ≥ N, Real.exp (m : ℝ) ≤ (a m : ℝ))
    (hn : N ≤ n) (hThalf : ReciprocalTail a n ≤ 1 / 2) :
    (PrefixProduct a n : ℝ) ^ 2 * SecondResidual a n ≤
      ResidualMajorant a n := by
  have hTn := reciprocalTail_le_ceilLog_add_geometric_div
    ha hamono hu hExp hn
  have hTnext := reciprocalTail_le_ceilLog_add_geometric_div
    ha hamono hu hExp (show N ≤ n + 1 by omega)
  have hE := secondResidual_le_eight_mul_tails ha hu hv hThalf
  have hP2 : 0 ≤ (PrefixProduct a n : ℝ) ^ 2 := sq_nonneg _
  have hT0 := reciprocalTail_nonneg ha n
  have hT10 := reciprocalTail_nonneg ha (n + 1)
  have hF0 : 0 ≤ TailRegularizer a n := (tailRegularizer_pos _ _).le
  have hF10 : 0 ≤ TailRegularizer a (n + 1) := (tailRegularizer_pos _ _).le
  have ha0 : (0 : ℝ) < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  have ha10 : (0 : ℝ) < (a (n + 1) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha (n + 1)))
  calc
    (PrefixProduct a n : ℝ) ^ 2 * SecondResidual a n ≤
        (PrefixProduct a n : ℝ) ^ 2 *
          (8 * ReciprocalTail a n * ReciprocalTail a (n + 1)) :=
      mul_le_mul_of_nonneg_left hE hP2
    _ ≤ (PrefixProduct a n : ℝ) ^ 2 *
          (8 * (TailRegularizer a n / (a n : ℝ)) *
            (TailRegularizer a (n + 1) / (a (n + 1) : ℝ))) := by
      gcongr
      · simpa [TailRegularizer] using hTn
      · simpa [TailRegularizer] using hTnext
    _ = ResidualMajorant a n := by
      rw [ResidualMajorant]
      field_simp
      ring

theorem residualMajorant_pos
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    0 < ResidualMajorant a n := by
  rw [ResidualMajorant]
  have hP : (0 : ℝ) < (PrefixProduct a n : ℝ) := by
    exact_mod_cast prefixProduct_pos ha n
  have ha0 : (0 : ℝ) < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  have ha1 : (0 : ℝ) < (a (n + 1) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha (n + 1)))
  have hF : 0 < 2 * TailRegularizer a n :=
    mul_pos (by norm_num) (tailRegularizer_pos _ _)
  have hF1 : 0 < 2 * TailRegularizer a (n + 1) :=
    mul_pos (by norm_num) (tailRegularizer_pos _ _)
  have hnum : 0 < 2 * (PrefixProduct a n : ℝ) ^ 2 *
      (2 * TailRegularizer a n) * (2 * TailRegularizer a (n + 1)) :=
    mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hP)) hF) hF1
  exact div_pos hnum (mul_pos ha0 ha1)

theorem log_residualMajorant
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (n : ℕ) :
    Real.log (ResidualMajorant a n) =
      Real.log 2 + 2 * Real.log (PrefixProduct a n : ℝ) +
        Real.log (2 * TailRegularizer a n) +
        Real.log (2 * TailRegularizer a (n + 1)) -
        Real.log (a n : ℝ) - Real.log (a (n + 1) : ℝ) := by
  have hP : (0 : ℝ) < (PrefixProduct a n : ℝ) := by
    exact_mod_cast prefixProduct_pos ha n
  have hF : 0 < 2 * TailRegularizer a n :=
    mul_pos (by norm_num) (tailRegularizer_pos _ _)
  have hF1 : 0 < 2 * TailRegularizer a (n + 1) :=
    mul_pos (by norm_num) (tailRegularizer_pos _ _)
  have ha0 : (0 : ℝ) < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha n))
  have ha1 : (0 : ℝ) < (a (n + 1) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) (ha (n + 1)))
  rw [ResidualMajorant]
  rw [Real.log_div (by positivity) (mul_pos ha0 ha1).ne']
  rw [Real.log_mul (by positivity) hF1.ne']
  rw [Real.log_mul (by positivity) hF.ne']
  rw [Real.log_mul (by norm_num) (sq_pos_of_pos hP).ne']
  rw [Real.log_mul ha0.ne' ha1.ne', Real.log_pow]
  norm_num
  ring

/-- In the positive-envelope branch the majorant, hence `P_n²E_n`, tends to
zero along the shifted indices. -/
theorem residualMajorant_shift_tendsto_zero
    {a : ℕ → ℕ} (ha : ∀ n, 2 ≤ a n) (hamono : Monotone a)
    (hu : Summable (ReciprocalTerm a))
    (hv : Summable (ShiftedReciprocalTerm a))
    {N : ℕ} {ell : ℝ} (hell : 0 < ell)
    (hlim : Tendsto
      (BinaryLogRatio (fun j ↦ TailEnvelope a (j + N))) atTop (𝓝 ell)) :
    Tendsto (fun j : ℕ ↦ ResidualMajorant a (j + N)) atTop (𝓝 0) := by
  have hB := positive_shifted_envelope_limit_cumulativeLog
    ha hamono hu hv hell hlim
  have hA := positive_shifted_envelope_limit_log_current
    ha hamono hu hv hell hlim
  obtain ⟨U, hU, hbound⟩ :=
    shifted_log_current_eventually_le_two_pow ha hamono hu hv hlim
  have hF := log_tailRegularizer_div_two_pow_tendsto_zero_of_bound ha hU hbound
  have hP : Tendsto
      (fun j : ℕ ↦ Real.log (PrefixProduct a (j + N) : ℝ) / (2 : ℝ) ^ j)
      atTop (𝓝 (ell / 2)) := by
    have hh := hB.sub hA
    convert hh using 1
    · funext j
      rw [BinaryLogRatio, log_prefixProduct ha (j + N)]
      rw [CumulativeLog, Finset.sum_range_succ]
      ring
    · ring_nf
  have hAsucc : Tendsto
      (fun j : ℕ ↦ Real.log (a (j + N + 1) : ℝ) / (2 : ℝ) ^ j)
      atTop (𝓝 ell) := by
    have hh := (hA.comp (tendsto_add_atTop_nat 1)).const_mul 2
    convert hh using 1
    · funext j
      simp only [Function.comp_apply]
      rw [BinaryLogRatio, pow_succ]
      have hind : j + N + 1 = j + 1 + N := by omega
      rw [hind]
      field_simp
    · ring_nf
  have hFsucc : Tendsto
      (fun j : ℕ ↦ Real.log (2 * TailRegularizer a (j + N + 1)) /
        (2 : ℝ) ^ j) atTop (𝓝 0) := by
    have hh := (hF.comp (tendsto_add_atTop_nat 1)).const_mul 2
    convert hh using 1
    · funext j
      simp only [Function.comp_apply]
      rw [pow_succ]
      have hind : j + N + 1 = j + 1 + N := by omega
      rw [hind]
      field_simp
    · simp
  have hconst : Tendsto (fun j : ℕ ↦ Real.log 2 / (2 : ℝ) ^ j)
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hcomb :=
    ((((hconst.add (hP.const_mul 2)).add hF).add hFsucc).sub hA).sub hAsucc
  have hloglim : Tendsto
      (fun j : ℕ ↦ Real.log (ResidualMajorant a (j + N)) / (2 : ℝ) ^ j)
      atTop (𝓝 (-ell / 2)) := by
    convert hcomb using 1
    · funext j
      rw [log_residualMajorant ha (j + N)]
      rw [BinaryLogRatio]
      field_simp
    · ring_nf
  apply tendsto_zero_of_normalized_log_tendsto_neg
    (fun j ↦ residualMajorant_pos ha (j + N)) (by linarith) hloglim

/-- The positive-limit branch is impossible: the second residual is both a
positive rational gap of denominator at most `bd P_n²` and, after the
regularized tail estimates, strictly smaller than that gap. -/
theorem positive_shifted_envelope_limit_impossible
    {a : ℕ → ℕ} (ha : IsRationalPairSequence a)
    {N : ℕ} {ell : ℝ} (hell : 0 < ell)
    (hlim : Tendsto
      (BinaryLogRatio (fun j ↦ TailEnvelope a (j + N))) atTop (𝓝 ell)) :
    False := by
  have ha2 : ∀ n, 2 ≤ a n := two_le_of_isRationalPairSequence ha
  have hamono : Monotone a := ha.1.monotone
  have hu : Summable (ReciprocalTerm a) :=
    summable_reciprocalTerm_of_admissible ha
  have hv : Summable (ShiftedReciprocalTerm a) :=
    summable_shiftedReciprocalTerm_of_admissible ha
  obtain ⟨b, d, hb, hd, hintT, hintV⟩ :=
    exists_integral_scales_for_two_tails ha
  have hbdZ : 0 < b * d := mul_pos hb hd
  have hbd : (0 : ℝ) < ((b * d : ℤ) : ℝ) := by exact_mod_cast hbdZ
  have hExpEvent := positive_shifted_envelope_limit_forces_exp_growth
    ha2 hamono hu hv hell hlim
  obtain ⟨Ne, hNe⟩ := eventually_atTop.1 hExpEvent
  have hMlim := residualMajorant_shift_tendsto_zero
    ha2 hamono hu hv hell hlim
  have hMsmall : ∀ᶠ j : ℕ in atTop,
      ResidualMajorant a (j + N) < 1 / ((b * d : ℤ) : ℝ) :=
    (tendsto_order.1 hMlim).2 _ (one_div_pos.mpr hbd)
  have hTlim : Tendsto (fun j : ℕ ↦ ReciprocalTail a (j + N))
      atTop (𝓝 0) :=
    (reciprocalTail_tendsto_zero a).comp (tendsto_add_atTop_nat N)
  have hTsmall : ∀ᶠ j : ℕ in atTop,
      ReciprocalTail a (j + N) < 1 / 2 :=
    (tendsto_order.1 hTlim).2 _ (by norm_num)
  have hgood : ∀ᶠ j : ℕ in atTop,
      ResidualMajorant a (j + N) < 1 / ((b * d : ℤ) : ℝ) ∧
      ReciprocalTail a (j + N) < 1 / 2 ∧ Ne ≤ j := by
    filter_upwards [hMsmall, hTsmall, eventually_ge_atTop Ne] with j hjM hjT hjNe
    exact ⟨hjM, hjT, hjNe⟩
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hgood
  obtain ⟨hMJ, hTJ, hNeJ⟩ := hJ J le_rfl
  have hNeShift : Ne ≤ J + N := by omega
  have hEpos : 0 < SecondResidual a (J + N) :=
    secondResidual_pos ha2 hamono hu hv (lt_trans hTJ (by norm_num))
  have hlower := one_le_scales_mul_prefix_sq_mul_secondResidual
    ha2 hu hb hd hintT hintV
    (lt_trans hTJ (by norm_num)) hEpos
  have hupper := prefix_sq_mul_secondResidual_le_majorant
    ha2 hamono hu hv hNe hNeShift hTJ.le
  have hstrict :
      ((b * d : ℤ) : ℝ) * (PrefixProduct a (J + N) : ℝ) ^ 2 *
          SecondResidual a (J + N) < 1 := by
    calc
      ((b * d : ℤ) : ℝ) * (PrefixProduct a (J + N) : ℝ) ^ 2 *
            SecondResidual a (J + N) =
          ((b * d : ℤ) : ℝ) *
            ((PrefixProduct a (J + N) : ℝ) ^ 2 *
              SecondResidual a (J + N)) := by ring
      _ ≤ ((b * d : ℤ) : ℝ) * ResidualMajorant a (J + N) :=
        mul_le_mul_of_nonneg_left hupper hbd.le
      _ < ((b * d : ℤ) : ℝ) * (1 / ((b * d : ℤ) : ℝ)) :=
        mul_lt_mul_of_pos_left hMJ hbd
      _ = 1 := by field_simp
  exact (not_lt_of_ge hlower) hstrict

end Erdos265

/-!
# Erdős Problem 265: assembly

The eventual quadratic recurrence gives a shifted binary-normalized envelope
limit `ell ≥ 0`.  If `ell = 0`, the envelope directly controls the original
sequence.  If `ell > 0`, the second-residual contradiction rules it out.
-/

open Filter Topology

namespace Erdos265

/-- The zero-limit envelope branch implies the unshifted critical logarithmic
conclusion.  The domination by the next envelope value is only eventual, which
is sufficient for the squeeze argument. -/
theorem criticalBaseTwoConclusion_of_zero_shifted_envelope_limit
    {a : ℕ → ℕ} (ha : IsRationalPairSequence a)
    {N : ℕ}
    (hlim : Tendsto
      (BinaryLogRatio (fun j ↦ TailEnvelope a (j + N))) atTop (𝓝 0)) :
    CriticalBaseTwoConclusion a := by
  have ha2 : ∀ n, 2 ≤ a n := two_le_of_isRationalPairSequence ha
  have hamono : Monotone a := ha.1.monotone
  have hu : Summable (ReciprocalTerm a) :=
    summable_reciprocalTerm_of_admissible ha
  have hv : Summable (ShiftedReciprocalTerm a) :=
    summable_shiftedReciprocalTerm_of_admissible ha
  have hHshift : Tendsto
      (fun j : ℕ ↦
        2 * BinaryLogRatio (fun r ↦ TailEnvelope a (r + N)) (j + 1))
      atTop (𝓝 0) := by
    simpa using (hlim.comp (tendsto_add_atTop_nat 1)).const_mul 2
  obtain ⟨Nt, hNt⟩ :=
    eventually_atTop.1 (eventually_reciprocalTail_le_one a)
  have htail : ∀ᶠ j : ℕ in atTop,
      ReciprocalTail a (j + N + 1) ≤ 1 :=
    (eventually_ge_atTop Nt).mono fun j hj ↦ hNt _ (by omega)
  have hAshift : Tendsto
      (BinaryLogRatio (fun j ↦ (a (j + N) : ℝ))) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun j ↦ by
        have haOne : 1 ≤ a (j + N) :=
          le_trans (by norm_num) (ha2 (j + N))
        rw [BinaryLogRatio]
        exact div_nonneg
          (Real.log_nonneg (by exact_mod_cast haOne)) (by positivity)
    · filter_upwards [htail] with j hj
      have hdom : (a (j + N) : ℝ) ≤ TailEnvelope a (j + N + 1) :=
        current_le_tailEnvelope_succ_of_tail_le_one
          ha2 hamono hu hv (by simpa [Nat.add_assoc] using hj)
      have haPos : (0 : ℝ) < (a (j + N) : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by omega) (ha2 (j + N)))
      have hlog : Real.log (a (j + N) : ℝ) ≤
          Real.log (TailEnvelope a (j + N + 1)) :=
        Real.log_le_log haPos hdom
      have hp : 0 ≤ (2 : ℝ) ^ j := by positivity
      calc
        BinaryLogRatio (fun r ↦ (a (r + N) : ℝ)) j ≤
            Real.log (TailEnvelope a (j + N + 1)) / (2 : ℝ) ^ j :=
          div_le_div_of_nonneg_right hlog hp
        _ = 2 * BinaryLogRatio
            (fun r ↦ TailEnvelope a (r + N)) (j + 1) := by
          rw [BinaryLogRatio, pow_succ]
          have hind : j + N + 1 = j + 1 + N := by omega
          rw [hind]
          field_simp
    · exact hHshift
  have hcriticalShift : Tendsto
      (fun j : ℕ ↦ CriticalLogRatio a (j + N)) atTop (𝓝 0) := by
    have hh := hAshift.div_const ((2 : ℝ) ^ N)
    convert hh using 1
    · funext j
      rw [CriticalLogRatio, BinaryLogRatio, pow_add]
      field_simp
    · simp
  exact (tendsto_add_atTop_iff_nat N).1 hcriticalShift

/-- Kernel-checked critical-base-two conclusion for every admissible pair of
rational reciprocal sums. -/
theorem erdos265_criticalBaseTwoConclusion
    {a : ℕ → ℕ} (ha : IsRationalPairSequence a) :
    CriticalBaseTwoConclusion a := by
  have ha2 : ∀ n, 2 ≤ a n := two_le_of_isRationalPairSequence ha
  have hamono : Monotone a := ha.1.monotone
  have hu : Summable (ReciprocalTerm a) :=
    summable_reciprocalTerm_of_admissible ha
  have hv : Summable (ShiftedReciprocalTerm a) :=
    summable_shiftedReciprocalTerm_of_admissible ha
  obtain ⟨C, hC, hint⟩ := admissible_has_integral_difference_scale ha
  let K : ℝ := 4 * Real.sqrt (C : ℝ)
  have hCreal : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hConeZ : (1 : ℤ) ≤ C := by omega
  have hCone : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hConeZ
  have hsqrtSq : (Real.sqrt (C : ℝ)) ^ 2 = (C : ℝ) :=
    Real.sq_sqrt hCreal.le
  have hsqrtNonneg : 0 ≤ Real.sqrt (C : ℝ) := Real.sqrt_nonneg _
  have hsqrtOne : 1 ≤ Real.sqrt (C : ℝ) := by nlinarith
  have hKone : 1 ≤ K := by
    dsimp [K]
    nlinarith
  have hHpos : ∀ n, 0 < TailEnvelope a n :=
    tailEnvelope_pos ha2 hu hv
  have hrec : ∀ᶠ n in atTop,
      TailEnvelope a (n + 1) ≤ K * (TailEnvelope a n) ^ 2 := by
    simpa [K] using
      eventually_tailEnvelope_square_recurrence ha2 hamono hu hv hC hint
  have hge : ∀ᶠ n in atTop, 1 ≤ K * TailEnvelope a n :=
    (eventually_one_le_tailEnvelope ha2 hamono hu hv).mono fun n hn ↦ by
      calc
        1 ≤ K := hKone
        _ = K * 1 := by ring
        _ ≤ K * TailEnvelope a n :=
          mul_le_mul_of_nonneg_left hn hK.le
  obtain ⟨N, ell, hell, hlim⟩ :=
    eventual_quadratic_has_shifted_limit hK hHpos hrec hge
  rcases eq_or_lt_of_le hell with hzero | hpositive
  · rw [← hzero] at hlim
    exact criticalBaseTwoConclusion_of_zero_shifted_envelope_limit ha hlim
  · exact (positive_shifted_envelope_limit_impossible ha hpositive hlim).elim

/-- Bundled internal form of the negative answer. -/
theorem erdos265_negative_answer_of_admissible
    {a : ℕ → ℕ} (ha : IsRationalPairSequence a) :
    ¬ GrowthExceedsOne a :=
  criticalBaseTwoConclusion_implies_negative_answer ha
    (erdos265_criticalBaseTwoConclusion ha)

/-- Fully expanded negative answer to the target question: there is no
admissible sequence whose critical base-two growth stays above a fixed
constant greater than one infinitely often. -/
theorem erdos265_negative_answer :
    ¬ ∃ a : ℕ → ℕ,
      StrictMono a ∧
      2 ≤ a 0 ∧
      Summable (fun n : ℕ ↦ (1 : ℝ) / (a n : ℝ)) ∧
      Summable (fun n : ℕ ↦ (1 : ℝ) / ((a n : ℝ) - 1)) ∧
      (∃ q : ℚ, ∑' n : ℕ, (1 : ℝ) / (a n : ℝ) = (q : ℝ)) ∧
      (∃ q : ℚ, ∑' n : ℕ,
        (1 : ℝ) / ((a n : ℝ) - 1) = (q : ℝ)) ∧
      ∃ c : ℝ, 1 < c ∧ ∃ᶠ n in atTop,
        c ^ (2 ^ n) ≤ (a n : ℝ) := by
  rintro ⟨a, h_strictMono, h_two_le,
    h_summable_reciprocal, h_summable_shifted,
    h_rational_reciprocal, h_rational_shifted, h_growth⟩
  exact (erdos265_negative_answer_of_admissible
    (a := a) ⟨h_strictMono, h_two_le,
      h_summable_reciprocal, h_summable_shifted,
      h_rational_reciprocal, h_rational_shifted⟩) h_growth

end Erdos265

#check Erdos265.erdos265_criticalBaseTwoConclusion
#print axioms Erdos265.erdos265_criticalBaseTwoConclusion
#check Erdos265.erdos265_negative_answer
#print axioms Erdos265.erdos265_negative_answer

/-! ## Added fidelity interface (2026-10-04)
All ordinary sums in the public interface below use `HasSum`.
`CriticalRoot` uses zero-based indices; `SourceCriticalRoot` uses the source's
one-based exponent for the same enumerated terms.
-/
namespace Erdos265

def SourceAdmissible (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ 2 ≤ a 0 ∧
    ∃ q r : ℚ,
      HasSum (fun n : ℕ ↦ (1 : ℝ) / (a n : ℝ)) (q : ℝ) ∧
      HasSum (fun n : ℕ ↦ (1 : ℝ) / ((a n : ℝ) - 1)) (r : ℝ)

theorem sourceAdmissible_iff (a : ℕ → ℕ) :
    SourceAdmissible a ↔ IsRationalPairSequence a := by
  constructor
  · rintro ⟨hm, h2, q, r, hq, hr⟩
    exact ⟨hm, h2, hq.summable, hr.summable,
      ⟨q, hq.tsum_eq⟩, ⟨r, hr.tsum_eq⟩⟩
  · rintro ⟨hm, h2, hu, hv, ⟨q, hq⟩, ⟨r, hr⟩⟩
    exact ⟨hm, h2, q, r, hq ▸ hu.hasSum, hr ▸ hv.hasSum⟩

noncomputable def CriticalRoot (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.rpow (a n : ℝ) (1 / (2 : ℝ) ^ n)

noncomputable def SourceCriticalRoot (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.rpow (a n : ℝ) (1 / (2 : ℝ) ^ (n + 1))

theorem criticalRoot_eq_exp {a : ℕ → ℕ}
    (ha : ∀ n, 0 < (a n : ℝ)) (n : ℕ) :
    CriticalRoot a n = Real.exp (CriticalLogRatio a n) := by
  rw [CriticalRoot, Real.rpow_eq_pow, Real.rpow_def_of_pos (ha n), CriticalLogRatio]
  congr 1
  ring

theorem sourceCriticalRoot_eq_exp {a : ℕ → ℕ}
    (ha : ∀ n, 0 < (a n : ℝ)) (n : ℕ) :
    SourceCriticalRoot a n = Real.exp (CriticalLogRatio a n / 2) := by
  rw [SourceCriticalRoot, Real.rpow_eq_pow, Real.rpow_def_of_pos (ha n), CriticalLogRatio, pow_succ]
  congr 1
  ring

/-- The literal root conclusion for the zero-based normalization. -/
theorem erdos265_root_limit {a : ℕ → ℕ} (ha : SourceAdmissible a) :
    Tendsto (CriticalRoot a) atTop (𝓝 1) := by
  have had := (sourceAdmissible_iff a).1 ha
  have hlog := erdos265_criticalBaseTwoConclusion had
  have h := Real.continuous_exp.continuousAt.tendsto.comp hlog
  simpa only [Function.comp_def, ← criticalRoot_eq_exp
    (positive_of_isRationalPairSequence had), Real.exp_zero] using h

/-- Literal one-based source exponents, retaining every term. -/
theorem erdos265_source_root_limit {a : ℕ → ℕ} (ha : SourceAdmissible a) :
    Tendsto (SourceCriticalRoot a) atTop (𝓝 1) := by
  have had := (sourceAdmissible_iff a).1 ha
  have hlog := (erdos265_criticalBaseTwoConclusion had).div_const 2
  have h := Real.continuous_exp.continuousAt.tendsto.comp hlog
  simpa only [Function.comp_def, ← sourceCriticalRoot_eq_exp
    (positive_of_isRationalPairSequence had), zero_div, Real.exp_zero] using h

/-- Extended-real limsup avoids conditional completeness conventions for
unbounded real sequences. -/
theorem erdos265_source_limsup {a : ℕ → ℕ} (ha : SourceAdmissible a) :
    Filter.limsup (fun n ↦ (SourceCriticalRoot a n : EReal)) atTop = 1 := by
  have h := EReal.tendsto_coe.mpr (erdos265_source_root_limit ha)
  simpa using h.limsup_eq

/-- The literal critical question. This definition alone is not a proof. -/
def CriticalQuestion : Prop :=
  ∃ a : ℕ → ℕ, SourceAdmissible a ∧
    1 < Filter.limsup (fun n ↦ (SourceCriticalRoot a n : EReal)) atTop

/-- Reproduction of the negative answer, transferred to the literal source
root/limsup statement. -/
theorem erdos265_source_negative_answer : ¬ CriticalQuestion := by
  rintro ⟨a, ha, hg⟩
  rw [erdos265_source_limsup ha] at hg
  exact lt_irrefl _ hg

/-- Fully expanded public theorem; rational sums are actual convergent sums. -/
theorem erdos265_faithful
    (a : ℕ → ℕ) (hm : StrictMono a) (h2 : 2 ≤ a 0)
    (q r : ℚ)
    (hq : HasSum (fun n : ℕ ↦ (1 : ℝ) / (a n : ℝ)) (q : ℝ))
    (hr : HasSum (fun n : ℕ ↦ (1 : ℝ) / ((a n : ℝ) - 1)) (r : ℝ)) :
    Tendsto (fun n : ℕ ↦ Real.rpow (a n : ℝ)
      (1 / (2 : ℝ) ^ (n + 1))) atTop (𝓝 1) :=
  erdos265_source_root_limit ⟨hm, h2, q, r, hq, hr⟩

end Erdos265

#print axioms Erdos265.sourceAdmissible_iff
#print axioms Erdos265.erdos265_faithful
#print axioms Erdos265.erdos265_source_limsup
#print axioms Erdos265.erdos265_source_negative_answer
