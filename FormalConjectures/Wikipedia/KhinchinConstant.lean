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
module

public import FormalConjecturesUtil

/-!
# Khinchin's Constant

For a real number $x$ with simple continued-fraction partial quotients $a_1, a_2, \dots$,
Aleksandr Yakovlevich Khinchin [Kh35] proved that for Lebesgue-almost every $x \in \mathbb{R}$,
the $n$-fold geometric mean $(a_1 a_2 \cdots a_n)^{1/n}$ converges as $n \to \infty$ to
$$K_0 = \prod_{r=1}^{\infty} \left(1 + \frac{1}{r(r + 2)}\right)^{\log_2 r} \approx 2.6854520010$$
([OEIS A002210](https://oeis.org/A002210)), called *Khinchin's constant*.

Whether $K_0$ is irrational or transcendental over $\mathbb{Q}$ remains unknown; likewise,
convergence $(a_1 \cdots a_n)^{1/n} \to K_0$ remains unproved for explicit constants such as $\pi$
or the Euler–Mascheroni constant $\gamma$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Khinchin%27s_constant#Open_problems)
- [OEIS A002210](https://oeis.org/A002210)
- [Kh35] A. Khintchine, *Metrische Kettenbruchprobleme*, Compositio Math. **1** (1935), 361–382.
-/

@[expose] public section

namespace KhinchinConstant

/-- Geometric mean $(a_1 a_2 \cdots a_n)^{1/n}$ formed from `Real.partQuot x k` over
$0 \le k < n$. -/
noncomputable def continuedFractionGeomMean (x : ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range n, Real.partQuot x k) ^ ((1 : ℝ) / (n : ℝ))

/-- Every factor `khinchinFactor r` is at least $1$. -/
@[category API, AMS 11 28]
theorem one_le_khinchinFactor (r : ℕ) : 1 ≤ khinchinFactor r := by
  unfold khinchinFactor
  split_ifs with hr
  · exact le_rfl
  · apply Real.one_le_rpow
    · have hpos : 0 < (r : ℝ) * ((r : ℝ) + 2) := by positivity
      linarith [one_div_pos.mpr hpos]
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr))
        (Real.log_nonneg (by norm_num))

/-- At $r = 0$, `khinchinFactor 0 = 1`. -/
@[category test, AMS 11 28]
theorem khinchinFactor_zero : khinchinFactor 0 = 1 := by
  simp [khinchinFactor]

/-- At $r = 1$, `khinchinFactor 1 = 1`. -/
@[category test, AMS 11 28]
theorem khinchinFactor_one : khinchinFactor 1 = 1 := by
  simp [khinchinFactor]

/-- At $r = 2$, `khinchinFactor 2 = 9 / 8`. -/
@[category test, AMS 11 28]
theorem khinchinFactor_two : khinchinFactor 2 = 9 / 8 := by
  unfold khinchinFactor
  rw [if_neg (by decide)]
  push_cast
  have hdiv : Real.log (2 : ℝ) / Real.log 2 = 1 :=
    div_self (ne_of_gt (Real.log_pos (by norm_num)))
  rw [hdiv, Real.rpow_one]
  norm_num

/-- Upper bound $\log(\mathrm{khinchinFactor}(r)) \le \frac{2}{\log 2} r^{-3/2}$ for all
$r \in \mathbb{N}$. -/
@[category API, AMS 11 28]
theorem log_khinchinFactor_le (r : ℕ) :
    Real.log (khinchinFactor r) ≤ (2 / Real.log 2) * ((r : ℝ) ^ (-(3 / 2 : ℝ))) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp [khinchinFactor]
  · have hr_pos : (0 : ℝ) < r := by positivity
    unfold khinchinFactor
    rw [if_neg hr0]
    have hbase_pos : 0 < 1 + 1 / ((r : ℝ) * ((r : ℝ) + 2)) := by positivity
    rw [Real.log_rpow hbase_pos]
    have hlog1 : Real.log (1 + 1 / ((r : ℝ) * ((r : ℝ) + 2))) ≤ 1 / (r : ℝ) ^ 2 := by
      calc Real.log (1 + 1 / ((r : ℝ) * ((r : ℝ) + 2)))
          ≤ (1 + 1 / ((r : ℝ) * ((r : ℝ) + 2))) - 1 := Real.log_le_sub_one_of_pos hbase_pos
        _ = 1 / ((r : ℝ) * ((r : ℝ) + 2)) := by ring
        _ ≤ 1 / (r : ℝ) ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have hlogr : Real.log (r : ℝ) ≤ 2 * (r : ℝ) ^ ((1 / 2 : ℝ)) := by
      have hsq : Real.sqrt (r : ℝ) = (r : ℝ) ^ ((1 / 2 : ℝ)) := Real.sqrt_eq_rpow (r : ℝ)
      have hsqrt_pos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hr_pos
      have h1 : Real.log (r : ℝ) = 2 * Real.log (Real.sqrt (r : ℝ)) := by
        rw [Real.log_sqrt hr_pos.le]
        ring
      have h2 : Real.log (Real.sqrt (r : ℝ)) ≤ Real.sqrt (r : ℝ) := by
        linarith [Real.log_le_sub_one_of_pos hsqrt_pos]
      rw [h1, ← hsq]
      linarith [h2]
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hnonneg1 : 0 ≤ Real.log (1 + 1 / ((r : ℝ) * ((r : ℝ) + 2))) :=
      Real.log_nonneg (by
        have : 0 < 1 / ((r : ℝ) * ((r : ℝ) + 2)) := by positivity
        linarith)
    calc Real.log (r : ℝ) / Real.log 2 * Real.log (1 + 1 / ((r : ℝ) * ((r : ℝ) + 2)))
        ≤ (2 * (r : ℝ) ^ ((1 / 2 : ℝ)) / Real.log 2) * (1 / (r : ℝ) ^ 2) := by
          apply mul_le_mul (div_le_div_of_nonneg_right hlogr hlog2_pos.le) hlog1 hnonneg1
          positivity
      _ = (2 / Real.log 2) * ((r : ℝ) ^ ((1 / 2 : ℝ)) * (r : ℝ) ^ (-2 : ℝ)) := by
          have hrpow2 : 1 / (r : ℝ) ^ 2 = (r : ℝ) ^ (-2 : ℝ) := by
            rw [Real.rpow_neg hr_pos.le, Real.rpow_two, one_div]
          rw [hrpow2]
          ring
      _ = (2 / Real.log 2) * ((r : ℝ) ^ (-(3 / 2 : ℝ))) := by
          rw [← Real.rpow_add hr_pos]
          norm_num

/-- `Real.log ∘ khinchinFactor` is summable over $\mathbb{N}$. -/
@[category API, AMS 11 28]
theorem summable_log_khinchinFactor :
    Summable (fun r : ℕ => Real.log (khinchinFactor r)) := by
  have hbound : Summable (fun r : ℕ => (2 / Real.log 2) * ((r : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    Summable.mul_left _ (Real.summable_nat_rpow.mpr (by norm_num))
  exact Summable.of_nonneg_of_le
    (fun r => Real.log_nonneg (one_le_khinchinFactor r)) log_khinchinFactor_le hbound

/-- Infinite product identity for `khinchinFactor` via the exponential of its log-series. -/
@[category API, AMS 11 28]
theorem hasProd_khinchinFactor :
    HasProd khinchinFactor (Real.exp (∑' r : ℕ, Real.log (khinchinFactor r))) := by
  have hhasProd : HasProd (Real.exp ∘ fun r : ℕ => Real.log (khinchinFactor r))
      (Real.exp (∑' r : ℕ, Real.log (khinchinFactor r))) :=
    summable_log_khinchinFactor.hasSum.rexp
  have hfun : (Real.exp ∘ fun r : ℕ => Real.log (khinchinFactor r)) = khinchinFactor := by
    ext r
    exact Real.exp_log (by linarith [one_le_khinchinFactor r])
  rwa [hfun] at hhasProd

/-- `khinchinFactor` is multipliable over $\mathbb{N}$. -/
@[category API, AMS 11 28]
theorem multipliable_khinchinFactor : Multipliable khinchinFactor := by
  exact hasProd_khinchinFactor.multipliable

/-- Lower bound $9 / 8 \le K_0$ from the $r = 2$ factor. -/
@[category test, AMS 11 28]
theorem nine_div_eight_le_khinchinConstant : (9 / 8 : ℝ) ≤ khinchinConstant := by
  unfold khinchinConstant
  rw [hasProd_khinchinFactor.tprod_eq]
  have hterm2 : Real.log (9 / 8 : ℝ) ≤ ∑' r : ℕ, Real.log (khinchinFactor r) := by
    have hle := summable_log_khinchinFactor.le_tsum 2
      (fun i _ => Real.log_nonneg (one_le_khinchinFactor i))
    rwa [khinchinFactor_two] at hle
  calc (9 / 8 : ℝ) = Real.exp (Real.log (9 / 8 : ℝ)) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (∑' r : ℕ, Real.log (khinchinFactor r)) := Real.exp_le_exp.mpr hterm2

/-- At length $n = 0$, `continuedFractionGeomMean x 0 = 1`. -/
@[category API, AMS 11 28]
theorem continuedFractionGeomMean_zero (x : ℝ) :
    continuedFractionGeomMean x 0 = 1 := by
  simp [continuedFractionGeomMean]

/-- For $x = 1/3$ at $n = 1$, the initial partial quotient is $a_1 = 3$, giving
`continuedFractionGeomMean (1 / 3) 1 = 3`. -/
@[category test, AMS 11 28]
theorem continuedFractionGeomMean_one_third_one :
    continuedFractionGeomMean (1 / 3 : ℝ) 1 = 3 := by
  unfold continuedFractionGeomMean Real.partQuot
  rw [Finset.prod_range_one]
  have hfrac : Int.fract (1 / 3 : ℝ) = 1 / 3 := by
    rw [Int.fract_eq_self]
    constructor <;> norm_num
  have hne : Int.fract (1 / 3 : ℝ) ≠ 0 := by
    rw [hfrac]
    norm_num
  have hfl : ⌊(Int.fract (1 / 3 : ℝ))⁻¹⌋ = 3 := by
    rw [hfrac]
    norm_num
  have hs0 : (GenContFract.of (1 / 3 : ℝ)).s.get? 0 = some ⟨1, 3⟩ := by
    change (GenContFract.of (1 / 3 : ℝ)).s.head = _
    rw [GenContFract.of_s_head hne, hfl]
    norm_num
  have hget : (GenContFract.of (1 / 3 : ℝ)).partDens.get? 0 = some (3 : ℝ) := by
    rw [GenContFract.partDens, Stream'.Seq.map_get?, hs0]
    norm_num
  rw [hget]
  norm_num

/-- Because $1/3 = [0; 3]$ terminates after one partial quotient, zero-padding at $k = 1$ gives
`continuedFractionGeomMean (1 / 3) 2 = 0`. -/
@[category test, AMS 11 28]
theorem continuedFractionGeomMean_one_third_two :
    continuedFractionGeomMean (1 / 3 : ℝ) 2 = 0 := by
  unfold continuedFractionGeomMean Real.partQuot
  rw [Finset.prod_range_succ, Finset.prod_range_one]
  have hfrac : Int.fract (1 / 3 : ℝ) = 1 / 3 := by
    rw [Int.fract_eq_self]
    constructor <;> norm_num
  have hne : Int.fract (1 / 3 : ℝ) ≠ 0 := by
    rw [hfrac]
    norm_num
  have hstream : GenContFract.IntFractPair.stream (1 / 3 : ℝ) 2 = none := by
    rw [GenContFract.IntFractPair.stream_succ hne 1, hfrac]
    have hinv : ((1 / 3 : ℝ))⁻¹ = ((3 : ℤ) : ℝ) := by norm_num
    rw [hinv]
    exact GenContFract.IntFractPair.stream_succ_of_int 3 0
  have hterm : (GenContFract.of (1 / 3 : ℝ)).TerminatedAt 1 :=
    GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr hstream
  have hs1 : (GenContFract.of (1 / 3 : ℝ)).s.get? 1 = none := hterm
  have hget1 : (GenContFract.of (1 / 3 : ℝ)).partDens.get? 1 = none := by
    rw [GenContFract.partDens, Stream'.Seq.map_get?, hs1]
    rfl
  rw [hget1]
  norm_num

/--
Khinchin's metric theorem [Kh35]: for Lebesgue-almost every real number $x$, the geometric mean
$(a_1 a_2 \cdots a_n)^{1/n}$ of its initial $n$ simple continued-fraction partial denominators
converges to Khinchin's constant $K_0$ as $n \to \infty$.
-/
@[category research solved, AMS 11 28]
theorem khinchin_geom_mean_ae :
    ∀ᵐ x : ℝ ∂MeasureTheory.volume,
      Filter.Tendsto (fun n : ℕ => continuedFractionGeomMean x n)
        Filter.atTop (nhds khinchinConstant) := by
  sorry

/--
Is Khinchin's constant $K_0 = \prod_{r=1}^{\infty} \bigl(1 + \frac{1}{r(r+2)}\bigr)^{\log_2 r}$
irrational?
-/
@[category research open, question, AMS 11 33]
theorem khinchin_constant_irrational : Irrational khinchinConstant := by
  sorry

/--
Is Khinchin's constant $K_0$ transcendental over $\mathbb{Q}$?
-/
@[category research open, question, AMS 11 33]
theorem khinchin_constant_irrational.variants.transcendental :
    Transcendental ℚ khinchinConstant := by
  sorry

/--
The geometric mean $(a_1 a_2 \cdots a_n)^{1/n}$ of the initial $n$ simple continued-fraction
partial denominators of $\pi$ converges to Khinchin's constant $K_0$ as $n \to \infty$.
-/
@[category research open, AMS 11 28]
theorem khinchin_geom_mean_pi :
    Filter.Tendsto (fun n : ℕ => continuedFractionGeomMean Real.pi n)
      Filter.atTop (nhds khinchinConstant) := by
  sorry

/--
The geometric mean $(a_1 a_2 \cdots a_n)^{1/n}$ of the initial $n$ simple continued-fraction
partial denominators of the Euler–Mascheroni constant $\gamma$ converges to Khinchin's constant
$K_0$ as $n \to \infty$.
-/
@[category research open, AMS 11 28]
theorem khinchin_geom_mean_eulerMascheroni :
    Filter.Tendsto (fun n : ℕ => continuedFractionGeomMean Real.eulerMascheroniConstant n)
      Filter.atTop (nhds khinchinConstant) := by
  sorry

end KhinchinConstant
