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

import FormalConjecturesUtil

/-!
# Erdős Problem 1099

*References:*
- [erdosproblems.com/1099](https://www.erdosproblems.com/1099)
- [Er81h] Erdős, P., Some problems and results on additive and multiplicative number theory.
  Analytic number theory (Philadelphia, Pa., 1980) (1981), 171-182.
- [Vo84] Vose, Michael D., Integers with consecutive divisors in small ratio. J. Number Theory
  (1984), 233-238.
-/

open Filter Finset Real
open scoped Topology

namespace Erdos1099

/-- $h_\alpha(n)=\sum_i (d_{i+1}/d_i-1)^\alpha$ over consecutive divisors of $n$, using the
increasing enumeration `Nat.nth (· ∈ n.divisors)` from ForMathlib. -/
noncomputable def h (α : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (n.divisors.card - 1), (n.consecutiveDivisorRatio i - 1) ^ α

/-- $\sum_i d_{i+1}/d_i$. -/
noncomputable def sumConsecutiveRatios (n : ℕ) : ℝ :=
  ∑ i ∈ range (n.divisors.card - 1), n.consecutiveDivisorRatio i

/--
Let $1=d_1<\cdots<d_{\tau(n)}=n$ be the divisors of $n$, and for $\alpha>1$ let
$$
h_\alpha(n) = \sum_i \left( \frac{d_{i+1}}{d_i}-1\right)^\alpha.
$$
Is it true that
$$
\liminf_{n\to \infty}h_\alpha(n) \ll_\alpha 1?
$$

A positive answer to the main question was provided by Vose [Vo84] by constructing a specific
sequence.
-/
@[category research solved, AMS 11]
theorem erdos_1099 :
    answer(True) ↔
      ∀ α > (1 : ℝ), ∃ C : ℝ, 0 < C ∧ liminf (fun n : ℕ ↦ h α n) atTop ≤ C := by
  sorry

/--
The $\liminf$ is trivially $\geq 1$, just considering the term $i=1$.
(Stated in `EReal` so the liminf is well-defined without an a-priori upper bound.)
-/
@[category textbook, AMS 11]
theorem erdos_1099.variants.liminf_ge_one (α : ℝ) (hα : 1 < α) :
    (1 : EReal) ≤ liminf (fun n : ℕ ↦ (h α n : EReal)) atTop := by
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : n ≠ 0 := by omega
  have h1mem : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
  have hnmem : n ∈ n.divisors := Nat.mem_divisors_self n hn0
  have hne : (1 : ℕ) ≠ n := by omega
  have hcard : 2 ≤ n.divisors.card := by
    refine Nat.succ_le_iff.mpr ?_
    exact Finset.one_lt_card.mpr ⟨1, h1mem, n, hnmem, hne⟩
  have h0 : (0 : ℕ) ∈ range (n.divisors.card - 1) := by
    simp only [mem_range]; omega
  have hnth2 : 2 ≤ Nat.nth (· ∈ n.divisors) 1 := by
    have hfin : (Set.ofPred (· ∈ n.divisors)).Finite := n.divisors.finite_toSet
    have hcard' : hfin.toFinset.card = n.divisors.card := by
      congr 1; ext x; simp [Set.Finite.mem_toFinset]
    refine Nat.two_le_nth_divisors hn0 (by decide) ?_
    refine ne_of_gt (Nat.pos_of_mem_divisors (Nat.nth_mem_of_lt_card hfin ?_))
    rw [hcard']; omega
  have hbase : (1 : ℝ) ≤ n.consecutiveDivisorRatio 0 - 1 := by
    rw [Nat.consecutiveDivisorRatio_zero hn0]
    have : (2 : ℝ) ≤ (Nat.nth (· ∈ n.divisors) 1 : ℝ) := Nat.cast_le.mpr hnth2
    linarith
  have hterm0 : (1 : ℝ) ≤ (n.consecutiveDivisorRatio 0 - 1) ^ α :=
    one_le_rpow hbase (le_of_lt (lt_trans Real.zero_lt_one hα))
  have hnonneg : ∀ i ∈ range (n.divisors.card - 1),
      (0 : ℝ) ≤ (n.consecutiveDivisorRatio i - 1) ^ α := by
    intro i hi
    have hi' : i + 1 < n.divisors.card := (Nat.lt_sub_iff_add_lt).mp (mem_range.mp hi)
    have hge1 : (1 : ℝ) ≤ n.consecutiveDivisorRatio i :=
      Nat.one_le_consecutiveDivisorRatio hi'
    exact Real.rpow_nonneg (sub_nonneg.mpr hge1) _
  have hR : (1 : ℝ) ≤ h α n := by
    calc
      (1 : ℝ) ≤ (n.consecutiveDivisorRatio 0 - 1) ^ α := hterm0
      _ ≤ ∑ i ∈ range (n.divisors.card - 1), (n.consecutiveDivisorRatio i - 1) ^ α :=
          single_le_sum hnonneg h0
      _ = h α n := rfl
  exact_mod_cast hR

theorem erdos_1099.variants.factorial :
    answer(sorry) ↔
      ∀ α > (1 : ℝ), ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, h α n.factorial ≤ C := by
  sorry

/--
Erdős [Er81h] remarks that the least common multiple of $\{1,\ldots,n\}$ would be a good candidate
for an infinite sequence of $n$ with $h_\alpha(n)$ bounded. It remains open whether this sequence
satisfies this property.
-/
@[category research open, AMS 11]
theorem erdos_1099.variants.lcm :
    answer(sorry) ↔
      ∀ α > (1 : ℝ), ∃ C : ℝ, 0 < C ∧
        ∀ n ≥ 1, h α ((Icc 1 n).lcm id) ≤ C := by
  sorry

/--
Erdős remarks that this problem occurred to him when considering $\sum_i \frac{d_{i+1}}{d_i}$.
It is easy to see that
$$
\sum_{i} \frac{d_{i+1}}{d_i}> \tau(n)+\log n,
$$
and Erdős asked whether
$$
\liminf \left(\sum_{i} \frac{d_{i+1}}{d_i}-\tau(n)-\log n\right)<\infty,
$$
which would follow from an affirmative answer to the main question.
-/
@[category research solved, AMS 11]
theorem erdos_1099.variants.sum_ratios :
    liminf (fun n : ℕ ↦
      (sumConsecutiveRatios n - (n.divisors.card : ℝ) - log n : EReal)) atTop < ⊤ := by
  sorry

/-- $h_\alpha(1)=0$ (a single divisor, empty sum). -/
@[category test, AMS 11]
theorem erdos_1099.variants.h_one (α : ℝ) : h α 1 = 0 := by
  simp [h, Nat.divisors_one]

/-- Empty consecutive-ratio sum for `n = 1`. -/
@[category test, AMS 11]
theorem erdos_1099.variants.sumConsecutiveRatios_one : sumConsecutiveRatios 1 = 0 := by
  simp [sumConsecutiveRatios, Nat.divisors_one]

/-- Consecutive-ratio sums are nonnegative. -/
@[category API, AMS 11]
theorem erdos_1099.variants.sumConsecutiveRatios_nonneg (n : ℕ) :
    0 ≤ sumConsecutiveRatios n := by
  classical
  exact Finset.sum_nonneg fun _ _ ↦ Nat.consecutiveDivisorRatio_nonneg _ _

end Erdos1099
