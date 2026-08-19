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
# Erdős Problem 1049

*References:*
- [erdosproblems.com/1049](https://www.erdosproblems.com/1049)
- [Er48] Erdős, P., On arithmetical properties of Lambert series. J. Indian Math. Soc. (N.S.)
  (1948), 63-66.
- [BV94] Bundschuh, P. and Väänänen, K., Arithmetical investigations of a certain infinite
  product. Compositio Math. 91 (1994), 175-199.
-/

namespace Erdos1049

open ArithmeticFunction Filter

/--
Let $t>1$ be a rational number. Is
$\sum_{n=1}^\infty\frac{1}{t^n-1}=\sum_{n=1}^\infty \frac{\tau(n)}{t^n}$ irrational, where
$\tau(n)$ counts the divisors of $n$?

A conjecture of Chowla.
-/
@[category research open, AMS 11]
theorem erdos_1049 :
    answer(sorry) ↔ ∀ t : ℚ, t > 1 → Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) := by
  sorry

/--
Erdős [Er48] proved that this is true if $t\geq 2$ is an integer.
-/
@[category research solved, AMS 11]
theorem erdos_1049.variants.geq_2_integer :
     ∀ t : ℤ, t ≥ 2 → Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) := by
  sorry

/--
Bundschuh and Väänänen [BV94, Theorem 2] proved a quantitative linear independence
result for $E_q$ and $E_q'$ whose $\alpha = -1$ case gives irrationality for a range
of non-integer rational bases.

Their parameter is $\lambda = \log h(t) / \log t$, where $h$ denotes the absolute
height; for $t = a/b > 1$ in lowest terms this is $\log a / \log(a/b)$. In the case
$\alpha = -1$ their Theorem 2 admits every $\lambda < (1/2 + 1/\pi^2)^{-1}$, and
$L_t(-1) = \sum_{j \geq 1} (t^j - 1)^{-1}$ is the series in question, so the
conclusion is its irrationality. Solving the condition on $\lambda$ for $a$ and $b$
gives the hypothesis below.

At $b = 1$ the hypothesis reads $0 < 1/2 - 1/\pi^2$, so this statement contains
`erdos_1049.variants.geq_2_integer`.
-/
@[category research solved, AMS 11]
theorem erdos_1049.variants.bundschuh_vaananen (t : ℚ) (ht : 1 < t)
    (hlam : Real.log t.den / Real.log t.num < 1 / 2 - 1 / Real.pi ^ 2) :
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) := by
  sorry

/--
The Bundschuh–Väänänen condition holds at $t = 7/2$, because
$$\frac{\log 2}{\log 7} < \frac{9}{25} < \frac{1}{2} - \frac{1}{\pi^2},$$
the first inequality since $2^{25} < 7^9$ and the second since $\pi^2 > 9$.

This is the smallest denominator-$2$ base the criterion reaches. The bases $a/2$
with $a$ odd and $1 < a/2 < 7/2$ are $3/2$ and $5/2$, and the condition fails at
both: see `erdos_1049.variants.bundschuh_vaananen_fails_at_three_halves`, and
$\log 2 / \log 5 > 2/5 > 1/2 - 1/\pi^2$ since $2^5 > 5^2$ and $\pi^2 < 10$.
-/
@[category research solved, AMS 11]
theorem erdos_1049.variants.seven_halves :
    Irrational (∑' n : ℕ+, 1 / (((7 / 2 : ℚ) : ℝ) ^ (n : ℕ) - 1)) := by
  refine erdos_1049.variants.bundschuh_vaananen (7 / 2) (by norm_num) ?_
  have hden : (((7 / 2 : ℚ)).den : ℝ) = 2 := by norm_num
  have hnum : (((7 / 2 : ℚ)).num : ℝ) = 7 := by norm_num
  rw [hden, hnum]
  have h7 : (0 : ℝ) < Real.log 7 := Real.log_pos (by norm_num)
  have key : (25 : ℝ) * Real.log 2 < 9 * Real.log 7 := by
    have h : Real.log ((2 : ℝ) ^ (25 : ℕ)) < Real.log ((7 : ℝ) ^ (9 : ℕ)) :=
      Real.log_lt_log (by positivity) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have h1 : Real.log 2 / Real.log 7 < 9 / 25 := by
    rw [div_lt_div_iff₀ h7 (by norm_num)]
    linarith
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : (9 : ℝ) < Real.pi ^ 2 := by nlinarith
  have hinv : 1 / Real.pi ^ 2 < 1 / 9 :=
    one_div_lt_one_div_of_lt (by norm_num) hpi2
  linarith

/--
The criterion in `erdos_1049.variants.bundschuh_vaananen` does not reach $t = 3/2$:
$$\frac{\log 2}{\log 3} > \frac{1}{2} > \frac{1}{2} - \frac{1}{\pi^2},$$
the first inequality since $3 < 2^2$.

So the smallest non-integer rational base lies outside the range covered by [BV94],
and `erdos_1049` is open there.
-/
@[category textbook, AMS 11]
theorem erdos_1049.variants.bundschuh_vaananen_fails_at_three_halves :
    ¬ (Real.log ((3 / 2 : ℚ)).den / Real.log ((3 / 2 : ℚ)).num
        < 1 / 2 - 1 / Real.pi ^ 2) := by
  have hden : (((3 / 2 : ℚ)).den : ℝ) = 2 := by norm_num
  have hnum : (((3 / 2 : ℚ)).num : ℝ) = 3 := by norm_num
  rw [hden, hnum, not_lt]
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have key : Real.log 3 < 2 * Real.log 2 := by
    have h : Real.log 3 < Real.log ((2 : ℝ) ^ (2 : ℕ)) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hhalf : (1 : ℝ) / 2 < Real.log 2 / Real.log 3 := by
    rw [lt_div_iff₀ h3]
    linarith
  have hpos : (0 : ℝ) < 1 / Real.pi ^ 2 := by positivity
  linarith

/--
Convergent case (`|t| > 1`).

Substitute `r := t⁻¹` so `‖r‖ < 1`, then apply Mathlib's series identity
`tsum_pow_div_one_sub_eq_tsum_sigma` at `k = 0`:
$$\sum_{n \ge 1} \frac{r^n}{1 - r^n} = \sum_{n \ge 1} \sigma_0(n) \cdot r^n.$$
After clearing denominators, both sides match the Lambert identity:
LHS becomes `1/(t^n - 1)` and RHS becomes `τ(n) / t^n`.
-/
@[category API, AMS 11]
private lemma lambert_convergent (t : ℝ) (ht : 1 < |t|) :
    ∑' n : ℕ+, 1 / (t ^ (n : ℕ) - 1) =
    ∑' n : ℕ+, ((n : ℕ).divisors.card : ℝ) / (t ^ (n : ℕ)) := by
  -- `|t| > 1` implies `t ≠ 0`, hence `t^n ≠ 0` for all n.
  have ht0 : t ≠ 0 := fun h => by subst h; simp at ht; linarith [abs_nonneg (0:ℝ)]
  have htn : ∀ n : ℕ, t ^ n ≠ 0 := fun n => pow_ne_zero n ht0
  -- Substitution `r := t⁻¹`, so `|r| < 1`.
  set r : ℝ := t⁻¹ with hr_def
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, hr_def, abs_inv]; exact inv_lt_one_of_one_lt₀ ht
  -- Apply the Mathlib identity. Now reduce each side of our goal to its form.
  have h := tsum_pow_div_one_sub_eq_tsum_sigma (k := 0) hr_norm
  convert h using 1
  -- LHS: show `1 / (t^n - 1) = r^n / (1 - r^n)`. After substituting `r = 1/t`,
  -- this is the algebraic identity `1/(t^n - 1) = (1/t^n) / (1 - 1/t^n)`,
  -- valid when `t^n ≠ 0` and `t^n ≠ 1`.
  · apply tsum_congr; intro n
    have hp : t ^ (n : ℕ) ≠ 0 := htn n
    have hrn : r ^ (n : ℕ) = (t ^ (n : ℕ))⁻¹ := by rw [hr_def, inv_pow]
    -- `t^n ≠ 1`: would imply `|t|^n = 1`, but `|t| > 1` gives `|t|^n > 1` since `n ≥ 1`.
    have hne1 : t ^ (n : ℕ) - 1 ≠ 0 := by
      intro hc
      have ht1 : t ^ (n : ℕ) = 1 := by linarith [sub_eq_zero.mp hc]
      have habs1 : |t| ^ (n : ℕ) = 1 := by rw [← abs_pow, ht1]; simp
      have hlt : 1 < |t| ^ (n : ℕ) := one_lt_pow₀ ht n.pos.ne'
      linarith
    rw [hrn]; field_simp
  -- RHS: `σ_0(n) · r^n = τ(n) / t^n` since `σ_0 = τ` and `r = 1/t`.
  · apply tsum_congr; intro n
    have hp : t ^ (n : ℕ) ≠ 0 := htn n
    have hrn : r ^ (n : ℕ) = (t ^ (n : ℕ))⁻¹ := by rw [hr_def, inv_pow]
    rw [hrn, ArithmeticFunction.sigma_zero_apply]; field_simp

/--
Divergent case (`|t| ≤ 1`).

Both `tsum`s equal `0` in this regime, but for different reasons in each
sub-case. We split on `t ∈ {1, 0, -1}` and the generic `|t| < 1, t ≠ 0`
remainder, and use the same `key` non-summability lemma below to handle
the cases where the series diverges.

- `t = 1`: every LHS term is `1 / (1 - 1) = 0` (Lean convention), so the
  LHS sum is trivially `0`. RHS is `Σ τ(n)`, non-summable.
- `t = 0`: every RHS term is `τ(n) / 0 = 0` (Lean convention), so the RHS
  sum is trivially `0`. LHS is `Σ (-1)`, non-summable.
- `t = -1`: alternating; LHS vanishes at even `n` but odd `n` give terms
  of magnitude `1/2`, an infinite set. RHS terms have magnitude `τ(n) ≥ 1`.
- `|t| < 1, t ≠ 0`: standard; bounded denominator gives lower-bounded
  reciprocal on LHS, and `|t^n| ≤ 1` plus `τ(n) ≥ 1` gives the RHS bound.

In every case, Lean's `tsum_eq_zero_of_not_summable` collapses the non-
summable side to `0`, matching the `0` on the other side.
-/
@[category API, AMS 11]
private lemma lambert_divergent (t : ℝ) (ht : |t| ≤ 1) :
    ∑' n : ℕ+, 1 / (t ^ (n : ℕ) - 1) =
    ∑' n : ℕ+, ((n : ℕ).divisors.card : ℝ) / (t ^ (n : ℕ)) := by
  -- `key`: a function with infinitely many terms bounded away from zero is
  -- not summable. Standard contrapositive of `Summable.tendsto_cofinite_zero`.
  have key : ∀ (f : ℕ+ → ℝ) (c : ℝ), 0 < c →
      Set.Infinite {n : ℕ+ | c ≤ |f n|} → ¬Summable f := by
    intro f c hc hinf hsum
    have h := hsum.tendsto_cofinite_zero
    rw [Metric.tendsto_nhds] at h
    have h1 := h c hc
    rw [Filter.eventually_cofinite] at h1
    refine hinf (h1.subset fun n hn => ?_)
    simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_lt]
    exact hn
  -- Number of divisors of `n ∈ ℕ+` is at least 1 (since `1 ∈ n.divisors`).
  have hcard_pos : ∀ (n : ℕ+), (1 : ℝ) ≤ ((n : ℕ).divisors.card : ℝ) := by
    intro n
    have : 0 < (n : ℕ).divisors.card := by
      apply Finset.card_pos.mpr
      exact ⟨1, Nat.one_mem_divisors.mpr n.2.ne'⟩
    exact_mod_cast this
  -- Case t = 1: LHS terms are 1/0 = 0 by Lean's convention, so LHS sum = 0.
  -- RHS terms are τ(n)/1 = τ(n) ≥ 1, so RHS is non-summable.
  by_cases ht1 : t = 1
  · subst ht1
    have hLzero : ∀ n : ℕ+, (1 : ℝ) / ((1 : ℝ) ^ (n : ℕ) - 1) = 0 := by intro n; simp
    rw [tsum_congr hLzero, tsum_zero]
    symm; apply tsum_eq_zero_of_not_summable
    apply key _ 1 (by norm_num)
    convert Set.infinite_univ (α := ℕ+)
    ext n
    simp only [one_pow, div_one, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [abs_of_nonneg (by positivity)]; exact hcard_pos n
  -- Case t = 0: RHS terms are τ(n)/0 = 0 by Lean's convention, so RHS sum = 0.
  -- LHS terms are 1/(0 - 1) = -1, so LHS is non-summable.
  by_cases ht0 : t = 0
  · subst ht0
    have hRzero : ∀ n : ℕ+, ((n : ℕ).divisors.card : ℝ) / ((0 : ℝ) ^ (n : ℕ)) = 0 := by
      intro n; rw [zero_pow n.pos.ne']; simp
    rw [tsum_congr hRzero, tsum_zero]
    apply tsum_eq_zero_of_not_summable
    apply key _ 1 (by norm_num)
    convert Set.infinite_univ (α := ℕ+)
    ext n
    simp only [zero_pow n.pos.ne', zero_sub, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    norm_num
  -- Case t = -1: alternating signs make `1/(t^n - 1)` vanish at even n but
  -- equal -1/2 at odd n. The set of odd `n ∈ ℕ+` is infinite, which is enough
  -- to invoke `key` on the LHS. RHS magnitude is τ(n) ≥ 1 everywhere.
  by_cases htneg1 : t = -1
  · subst htneg1
    -- Construct the infinite set of odd positive naturals via the injection
    -- `k ↦ 2k + 1`, which lands in `ℕ+` and is always odd.
    have hinf_odd : Set.Infinite {n : ℕ+ | Odd (n : ℕ)} := by
      apply Set.infinite_of_injective_forall_mem
        (f := fun k : ℕ => (⟨2 * k + 1, Nat.succ_pos _⟩ : ℕ+))
      · intro a b hab; rw [Subtype.mk.injEq] at hab; omega
      · intro k; show Odd (2 * k + 1); exact ⟨k, rfl⟩
    have hL : ¬ Summable (fun n : ℕ+ => 1 / (((-1 : ℝ)) ^ (n : ℕ) - 1)) := by
      apply key _ (1/2) (by norm_num)
      apply hinf_odd.mono
      intro n hn
      -- For odd n: (-1)^n = -1, so 1/((-1)^n - 1) = 1/(-2), magnitude 1/2.
      show (1/2 : ℝ) ≤ |1 / ((-1 : ℝ) ^ (n : ℕ) - 1)|
      rw [Odd.neg_one_pow hn]; norm_num
    have hR : ¬ Summable (fun n : ℕ+ => ((n : ℕ).divisors.card : ℝ) / ((-1 : ℝ) ^ (n : ℕ))) := by
      apply key _ 1 (by norm_num)
      convert Set.infinite_univ (α := ℕ+)
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      -- |(-1)^n| = 1, so |τ(n) / (-1)^n| = τ(n) ≥ 1.
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, div_one]
      rw [abs_of_nonneg (by positivity)]
      exact hcard_pos n
    rw [tsum_eq_zero_of_not_summable hL, tsum_eq_zero_of_not_summable hR]
  -- Remaining case: |t| ≤ 1 with t ∉ {1, 0, -1}, equivalently |t| < 1 and t ≠ 0.
  · -- First narrow `|t| ≤ 1` to `|t| < 1` using the case exclusions.
    have habs_lt : |t| < 1 := by
      rcases lt_or_eq_of_le ht with h | h
      · exact h
      · exfalso
        rcases (abs_eq zero_le_one).mp h with rfl | rfl
        · exact ht1 rfl
        · exact htneg1 rfl
    have habs_pos : 0 < |t| := abs_pos.mpr ht0
    -- Since `|t| < 1`, `|t^n| ≤ 1` for all `n ∈ ℕ+`.
    have hbound : ∀ (n : ℕ+), |t ^ (n : ℕ)| ≤ 1 := by
      intro n; rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (le_of_lt habs_lt)
    -- Since `|t| < 1` strictly, `t^n ≠ 1` (else `|t|^n = 1` but `|t|^n ≤ |t| < 1`).
    have htn_ne_one : ∀ (n : ℕ+), t ^ (n : ℕ) ≠ 1 := by
      intro n hn
      have h1 : |t ^ (n : ℕ)| = 1 := by rw [hn]; exact abs_one
      rw [abs_pow] at h1
      have hle : |t| ^ (n : ℕ) ≤ |t| := by
        exact pow_le_of_le_one (abs_nonneg _) (le_of_lt habs_lt) n.pos.ne'
      linarith
    have htn_ne_zero : ∀ (n : ℕ+), t ^ (n : ℕ) ≠ 0 := fun n => pow_ne_zero _ ht0
    -- LHS: `|t^n - 1| ≤ |t^n| + 1 ≤ 2`, so `|1 / (t^n - 1)| ≥ 1/2` everywhere.
    have hL : ¬ Summable (fun n : ℕ+ => 1 / (t ^ (n : ℕ) - 1)) := by
      apply key _ (1/2) (by norm_num)
      convert Set.infinite_univ (α := ℕ+)
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have hden_bound : |t ^ (n : ℕ) - 1| ≤ 2 := by
        calc |t ^ (n : ℕ) - 1| ≤ |t ^ (n : ℕ)| + |(1 : ℝ)| := abs_sub _ _
          _ ≤ 1 + 1 := by have := hbound n; rw [abs_one]; linarith
          _ = 2 := by norm_num
      have hden_pos : 0 < |t ^ (n : ℕ) - 1| := by
        rw [abs_pos, sub_ne_zero]; exact htn_ne_one n
      rw [abs_div, abs_one, le_div_iff₀ hden_pos]; linarith
    -- RHS: `|τ(n) / t^n| = τ(n) / |t^n| ≥ τ(n) ≥ 1` since `|t^n| ≤ 1`.
    have hR : ¬ Summable (fun n : ℕ+ => ((n : ℕ).divisors.card : ℝ) / (t ^ (n : ℕ))) := by
      apply key _ 1 (by norm_num)
      convert Set.infinite_univ (α := ℕ+)
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [abs_div, le_div_iff₀ (abs_pos.mpr (htn_ne_zero n))]
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n : ℕ).divisors.card : ℝ))]
      have := hbound n
      have := hcard_pos n
      nlinarith
    rw [tsum_eq_zero_of_not_summable hL, tsum_eq_zero_of_not_summable hR]

/--
The classical Lambert series identity: $\sum_{n=1}^\infty \frac{1}{t^n - 1} =
\sum_{n=1}^\infty \frac{\tau(n)}{t^n}$, where $\tau(n)$ counts the divisors of $n$.
-/
@[category textbook, AMS 11]
theorem lambert_series_eq_num_divisor_sum : ∀ t : ℚ,
     ∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1) =
     ∑' n : ℕ+, (n : ℕ).divisors.card / ((t : ℝ) ^ (n : ℕ)) := by
  intro t
  by_cases ht : 1 < |(t : ℝ)|
  · exact lambert_convergent (t : ℝ) ht
  · push_neg at ht
    exact lambert_divergent (t : ℝ) ht

end Erdos1049
