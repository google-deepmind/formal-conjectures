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
# Cramér's Conjecture on Prime Gaps

Write $p_n$ for the $n$-th prime (`Nat.nth Nat.Prime`, with $p_0 = 2$) and $g_n = p_{n+1} - p_n$
(`primeGap n`). Using an independent random prime heuristic, Harald Cramér [Cr36] conjectured in
1936 that $g_n = O((\log p_n)^2)$; his random model further predicts
$$\limsup_{n \to \infty} \frac{p_{n+1} - p_n}{(\log p_n)^2} = 1,$$
while numerical searches also test the strict inequality $g_n < (\log p_n)^2$ for $n \ge 4$
($p_n \ge 11$). Accounting for Helmut Maier's short-interval oscillations [Ma85] and small-prime
sieve factors, Andrew Granville [Gr95] conjectured instead that the limit superior is at least
$2 e^{-\gamma} \approx 1.1229$ (contradicting $\limsup = 1$). Unconditionally, Baker, Harman, and
Pintz [BHP01] proved $g_n = O(p_n^{0.525})$. See also `Erdos5`, `Erdos233`, `Andrica`, `Oppermann`,
and `Firoozbakht` (`Firoozbakht.firoozbakht_conjecture_consequence`).

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Cram%C3%A9r%27s_conjecture)
- [We31] E. Westzynthius (1931), Commentat. Phys.-Math. **5**, no. 25, 1–37.
- [Cr36] H. Cramér (1936), Acta Arith. **2**, no. 1, 23–46.
- [Ma85] H. Maier (1985), Michigan Math. J. **32**, no. 2, 221–225.
- [Gr95] A. Granville (1995), Scand. Actuar. J. **1995**, no. 1, 12–28.
- [BHP01] R. C. Baker, G. Harman, and J. Pintz (2001), Proc. London Math. Soc. (3) **83**, no. 3,
  532–562.
- [Al26] L. Alpöge, [Note on the Riemann Hypothesis](https://alpo.ge/remark.pdf) (2026).
-/

@[expose] public section

open scoped Asymptotics

namespace CramerConjecture

/-- Cramér's normalized prime-gap ratio $\dfrac{p_{n+1} - p_n}{(\log p_n)^2}$. Since $p_n \ge 2$
for all $n \in \mathbb{N}$, the denominator $(\log p_n)^2$ is always strictly positive. -/
noncomputable def cramerRatio (n : ℕ) : ℝ :=
  (primeGap n : ℝ) / (Real.log (Nat.nth Nat.Prime n)) ^ 2

/-- Each of $n = 0$ ($p_0 = 2, g_0 = 1$), $n = 1$ ($p_1 = 3, g_1 = 2$, ratio $\approx 1.657$),
and $n = 3$ ($p_3 = 7, p_4 = 11, g_3 = 4$) satisfies `1 < cramerRatio n`, showing that `4 ≤ n`
is sharp in `cramer_conjecture.variants.strict_bound`, with `cramerRatio 1 < 2`. -/
@[category test, AMS 11]
theorem cramerRatio_small_index_bounds :
    1 < cramerRatio 0 ∧ 1 < cramerRatio 1 ∧ cramerRatio 1 < 2 ∧ 1 < cramerRatio 3 := by
  have hg0 : primeGap 0 = 1 := by
    simp [primeGap, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  have hg1 : primeGap 1 = 2 := by
    simp [primeGap, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
  have hg3 : primeGap 3 = 4 := by
    simp [primeGap, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cramerRatio, hg0, Nat.nth_prime_zero_eq_two]
    have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    simpa using (one_lt_inv₀ (sq_pos_of_pos hpos)).mpr (by nlinarith)
  · rw [cramerRatio, hg1, Nat.nth_prime_one_eq_three]
    have hpos : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hpow : Real.log ((3 : ℝ) ^ 3) < 4 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr (by
      rw [show (4 : ℝ) = (4 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
      nlinarith [Real.exp_one_gt_d9, sq_nonneg (Real.exp 1 - 2.7)])
    rw [Real.log_pow] at hpow
    exact (one_lt_div (sq_pos_of_pos hpos)).mpr (by push_cast at hpow ⊢; nlinarith)
  · rw [cramerRatio, hg1, Nat.nth_prime_one_eq_three]
    have hgt1 : 1 < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
    exact (div_lt_iff₀ (by positivity)).mpr (by push_cast; nlinarith)
  · rw [cramerRatio, hg3, Nat.nth_prime_three_eq_seven]
    have hpos : 0 < Real.log 7 := Real.log_pos (by norm_num)
    have hlt2 : Real.log 7 < 2 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr
      (by rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith [Real.exp_one_gt_d9])
    exact (one_lt_div (sq_pos_of_pos hpos)).mpr (by push_cast; nlinarith)

/-- **Cramér's Conjecture** [Cr36]: consecutive prime differences satisfy
$p_{n+1} - p_n = O((\log p_n)^2)$ as $n \to \infty$. -/
@[category research open, AMS 11]
theorem cramer_conjecture :
    (fun n : ℕ => (primeGap n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => (Real.log (Nat.nth Nat.Prime n)) ^ 2) := by
  sorry

/-- **Cramér's Heuristic Limit-Superior Prediction**: $\limsup_{n \to \infty} g_n / (\log p_n)^2 =
1$. Rather than an explicit conjecture in [Cr36], this stronger statement comes from Cramér's
probabilistic prime model and contradicts `cramer_conjecture.variants.granville`
($2 e^{-\gamma} > 1$). -/
@[category research open, AMS 11]
theorem cramer_conjecture.variants.limsup_eq_one :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, cramerRatio n ≤ 1 + ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ᶠ n in Filter.atTop, 1 - ε ≤ cramerRatio n) := by
  sorry

/-- **Strong Numerical Cramér Inequality**: for every $n \ge 4$ ($p_n \ge 11$),
$p_{n+1} - p_n < (\log p_n)^2$ (indices $n \in \{0, 1, 3\}$ fail; see
`cramerRatio_small_index_bounds`, and compare `Firoozbakht.firoozbakht_conjecture_consequence` for
the stronger bound $p_{n+1} - p_n < (\log p_n)^2 - \log p_n$ on the same range). -/
@[category research open, AMS 11]
theorem cramer_conjecture.variants.strict_bound (n : ℕ) (hn : 4 ≤ n) :
    cramerRatio n < 1 := by
  sorry

/-- **Cramér–Granville Conjecture** [Gr95]: $\limsup_{n \to \infty} g_n / (\log p_n)^2 \ge
2 e^{-\gamma}$, stated without conditional `ℝ`-suprema as infinitely many $n$ satisfying
$\operatorname{cramerRatio}(n) \ge c$ for each $c < 2 e^{-\gamma}$ (contradicting
`limsup_eq_one` and `strict_bound`). -/
@[category research open, AMS 11]
theorem cramer_conjecture.variants.granville (c : ℝ)
    (hc : c < 2 * Real.exp (-Real.eulerMascheroniConstant)) :
    ∃ᶠ n : ℕ in Filter.atTop, c ≤ cramerRatio n := by
  sorry

/-- **Cramér's Conditional Prime Gap Bound** [Cr36]: under `RiemannHypothesis`,
$p_{n+1} - p_n = O(\sqrt{p_n} \log p_n)$. -/
@[category research solved, AMS 11]
theorem cramer_conjecture.variants.conditional_rh (hRH : RiemannHypothesis) :
    (fun n : ℕ => (primeGap n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => Real.sqrt (Nat.nth Nat.Prime n) * Real.log (Nat.nth Nat.Prime n)) := by
  sorry

/-- Cramér's bound $p_{n+1} - p_n = O(\sqrt{p_n} \log p_n)$
(`cramer_conjecture.variants.conditional_rh`) holds unconditionally, since the Riemann
hypothesis is proved [Al26]. -/
@[category research solved, AMS 11]
theorem cramer_conjecture.variants.sqrt_log_bound :
    (fun n : ℕ => (primeGap n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => Real.sqrt (Nat.nth Nat.Prime n) * Real.log (Nat.nth Nat.Prime n)) := by
  sorry

/-- **Westzynthius's Theorem** [We31] (cf. `Erdos5.erdos_5.variants.westzynthius`): for every real
$M$, infinitely many indices $n$ satisfy $p_{n+1} - p_n \ge M \log p_n$. -/
@[category research solved, AMS 11]
theorem cramer_conjecture.variants.westzynthius (M : ℝ) :
    ∃ᶠ n : ℕ in Filter.atTop,
      M * Real.log (Nat.nth Nat.Prime n : ℝ) ≤ (primeGap n : ℝ) := by
  sorry

/-- **Baker–Harman–Pintz Bound** [BHP01]: $p_{n+1} - p_n = O(p_n^{0.525})$ as $n \to \infty$. -/
@[category research solved, AMS 11]
theorem cramer_conjecture.variants.baker_harman_pintz :
    (fun n : ℕ => (primeGap n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) ^ (0.525 : ℝ)) := by
  sorry

end CramerConjecture
