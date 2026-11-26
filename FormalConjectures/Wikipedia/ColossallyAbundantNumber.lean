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
# Alaoglu–Erdős Conjectures on Colossally Abundant Numbers

On Wikipedia and in [OEIS A004490](https://oeis.org/A004490) ($2, 6, 12, 60, 120, 360, \dots$), an
integer $n > 1$ is called *colossally abundant* when some $\varepsilon > 0$ satisfies
$\sigma_1(n) / n^{1+\varepsilon} \ge \sigma_1(k) / k^{1+\varepsilon}$ for every $k > 1$. In their
1944 introduction [AE44, p. 448], Alaoglu and Erdős instead required $\ge$ for $1 \le m < n$ and
strict $>$ for $m > n$, selecting the greatest maximizer at $\varepsilon$. By contrast, the
inequalities on [AE44, p. 455] and the prime-exponent formula of [AE44, Theorem 10, p. 455] (where
$[x]$ denotes the largest integer $< x$) select the least maximizer ($>$ for $1 \le m < n$ and
$\ge$ for $m > n$, formalized as `IsAlaogluErdosColossallyAbundant` below), which defines the same
set as $\varepsilon > 0$ varies. Alaoglu and Erdős [AE44] predicted that consecutive colossally
abundant integers always differ by a prime factor, reducing this claim to showing that
$p^x, q^x \in \mathbb{Q}$ with distinct primes $p \ne q$ forces $x \in \mathbb{Z}$ (cf.
`Exponentials.four_exponentials_conjecture`). Combined with the six exponentials theorem of Lang
[La66] and Ramachandra [Ra68] (communicated for prime bases by Siegel in [AE44, p. 455]), [AE44]
yields unconditionally that consecutive [AE44] colossally abundant integers have prime or
squarefree-semiprime ratio, and that at most four integers $n > 1$ share any maximizer exponent
$\varepsilon > 0$ (studied further by Erdős and Nicolas [EN75]).

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Colossally_abundant_number)
- [AE44] L. Alaoglu and P. Erdős (1944), Trans. Amer. Math. Soc. **56**, 448–469.
- [La66] S. Lang (1966), *Introduction to Transcendental Numbers*, Addison-Wesley, Reading, Mass.
- [Ra68] K. Ramachandra (1968), Acta Arith. **14**, 65–72, 73–88.
- [EN75] P. Erdős and J.-L. Nicolas (1975), Bull. Soc. Math. France **103**, 65–90.
-/

@[expose] public section

namespace ColossallyAbundantNumber

open scoped ArithmeticFunction.sigma

/-- `IsColossallyAbundant n` holds when $n > 1$ maximizes $\sigma_1(k) / k^{1+\varepsilon}$ across
all $k > 1$ at some real exponent $\varepsilon > 0$. Because $n = 2$ uniquely dominates every
$k > 2$ whenever $\varepsilon > \log_2(3/2)$, restricting to $k > 1$ yields the same sequence
([OEIS A004490](https://oeis.org/A004490)) as maximizing over $k \ge 1$. -/
def IsColossallyAbundant (n : ℕ) : Prop :=
  1 < n ∧ ∃ ε : ℝ, 0 < ε ∧
    ∀ k : ℕ, 1 < k →
      (σ 1 k : ℝ) / (k : ℝ) ^ (1 + ε) ≤ (σ 1 n : ℝ) / (n : ℝ) ^ (1 + ε)

/-- `AreConsecutiveColossallyAbundant m n` holds when $m < n$ both satisfy `IsColossallyAbundant`
and no integer strictly between them does. -/
def AreConsecutiveColossallyAbundant (m n : ℕ) : Prop :=
  m < n ∧ IsColossallyAbundant m ∧ IsColossallyAbundant n ∧
    ∀ k : ℕ, m < k → k < n → ¬ IsColossallyAbundant k

/-- `IsAlaogluErdosColossallyAbundant n` holds when $n > 1$ is the least maximizer of
$\sigma_1(m) / m^{1+\varepsilon}$ at some $\varepsilon > 0$:
$\sigma_1(m) / m^{1+\varepsilon} < \sigma_1(n) / n^{1+\varepsilon}$ for $1 \le m < n$ and
$\sigma_1(m) / m^{1+\varepsilon} \le \sigma_1(n) / n^{1+\varepsilon}$ for $m > n$, matching the
inequalities on [AE44, p. 455] and the prime-exponent formula
$k_q(\varepsilon) = [\log((q^{1+\varepsilon} - 1) / (q^\varepsilon - 1)) / \log q] - 1$ of
[AE44, Theorem 10, p. 455], where $[x]$ denotes the largest integer $< x$ (giving $j - 2$ rather
than $\lfloor j \rfloor - 1 = j - 1$ at an integer $j$, thus choosing $q^{j-2}$ over $q^{j-1}$). By
contrast, [AE44, p. 448] imposes $\le$ on $1 \le m < n$ and $<$ on $m > n$ (picking the greatest
maximizer), whereas Wikipedia's `IsColossallyAbundant` uses $\le$ on both sides. Since
$\sigma_1(m) / m^{1+\varepsilon} \to 0$ as $m \to \infty$ uniformly on compact subsets of
$(0, \infty)$, only finitely many $m$ can contend near a given $\varepsilon$: nudging
$\varepsilon$ upward turns any least maximizer into the sole maximizer, while nudging
$\varepsilon$ downward isolates any greatest maximizer, so both one-sided definitions yield the
exact same set of integers as $\varepsilon > 0$ ranges over $(0, \infty)$. -/
def IsAlaogluErdosColossallyAbundant (n : ℕ) : Prop :=
  1 < n ∧ ∃ ε : ℝ, 0 < ε ∧
    (∀ m : ℕ, 1 ≤ m → m < n →
      (σ 1 m : ℝ) / (m : ℝ) ^ (1 + ε) < (σ 1 n : ℝ) / (n : ℝ) ^ (1 + ε)) ∧
    (∀ m : ℕ, n < m →
      (σ 1 m : ℝ) / (m : ℝ) ^ (1 + ε) ≤ (σ 1 n : ℝ) / (n : ℝ) ^ (1 + ε))

/-- `AreConsecutiveAlaogluErdosColossallyAbundant m n` holds when $m < n$ both satisfy
`IsAlaogluErdosColossallyAbundant` and no integer strictly between them does; because the
least-maximizer convention of [AE44, p. 455] and the greatest-maximizer convention of
[AE44, p. 448] define the same set across $\varepsilon > 0$, both notions of consecutiveness
coincide. -/
def AreConsecutiveAlaogluErdosColossallyAbundant (m n : ℕ) : Prop :=
  m < n ∧ IsAlaogluErdosColossallyAbundant m ∧ IsAlaogluErdosColossallyAbundant n ∧
    ∀ k : ℕ, m < k → k < n → ¬ IsAlaogluErdosColossallyAbundant k

/-- Every integer satisfying `IsAlaogluErdosColossallyAbundant` also satisfies Wikipedia's
non-strict `IsColossallyAbundant`. -/
@[category API, AMS 11]
theorem IsAlaogluErdosColossallyAbundant.isColossallyAbundant {n : ℕ}
    (h : IsAlaogluErdosColossallyAbundant n) : IsColossallyAbundant n := by
  rcases h with ⟨hn, ε, hε, hlt, hgt⟩
  refine ⟨hn, ε, hε, fun k hk => ?_⟩
  rcases lt_trichotomy k n with hkn | rfl | hnk
  · exact (hlt k (by omega) hkn).le
  · exact le_rfl
  · exact hgt k hnk

/-- $2$ is the least colossally abundant integer, witnessed at $\varepsilon = 1$. -/
@[category test, AMS 11]
theorem isColossallyAbundant_two : IsColossallyAbundant 2 := by
  refine ⟨by norm_num, 1, zero_lt_one, fun k hk => ?_⟩
  have hsub : k.divisors ⊆ Finset.range (k + 1) := fun d hd =>
    Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)))
  have hsig_le : σ 1 k ≤ ∑ i ∈ Finset.range (k + 1), i := by
    simpa [ArithmeticFunction.sigma_apply] using Finset.sum_le_sum_of_subset (f := id) hsub
  have hsum : (∑ i ∈ Finset.range (k + 1), i) * 2 = (k + 1) * k :=
    Finset.sum_range_id_mul_two (k + 1)
  have hquad_real : (4 : ℝ) * (σ 1 k : ℝ) ≤ 3 * ((k : ℝ) * (k : ℝ)) := by
    exact_mod_cast (by nlinarith : 4 * σ 1 k ≤ 3 * (k * k))
  rw [show σ 1 2 = 3 by decide, show (1 : ℝ) + 1 = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, Real.rpow_natCast]
  refine (div_le_div_iff₀ (by positivity) (by norm_num)).mpr ?_
  push_cast
  nlinarith

/-- Any integer $m > 2$ satisfying $2 \sigma_1(m) \le 3 m$ is strictly dominated by $k = 2$ at
every $\varepsilon > 0$, hence cannot be colossally abundant. -/
@[category API, AMS 11]
theorem not_isColossallyAbundant_of_two_mul_sigma_le {m : ℕ} (hm : 2 < m)
    (hsig : 2 * σ 1 m ≤ 3 * m) : ¬ IsColossallyAbundant m := by
  rintro ⟨_, ε, hε, hmax⟩
  have hle := hmax 2 (by norm_num)
  rw [show σ 1 2 = 3 by decide] at hle
  push_cast at hle
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos (by norm_num) _
  have hpm : (0 : ℝ) < (m : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos (by positivity) _
  replace hle := (div_le_div_iff₀ hp2 hpm).mp hle
  have hm_gt : (1 : ℝ) < (m : ℝ) / 2 := by
    have : (2 : ℝ) < m := by exact_mod_cast hm
    linarith
  have hpow := Real.rpow_lt_rpow_of_exponent_lt hm_gt (by linarith : (1 : ℝ) < 1 + ε)
  rw [Real.rpow_one, Real.div_rpow (by positivity) (by norm_num), lt_div_iff₀ hp2] at hpow
  have hsigR : (2 : ℝ) * (σ 1 m : ℝ) ≤ 3 * (m : ℝ) := by exact_mod_cast hsig
  nlinarith

/-- Neither $3$ nor $5$ is colossally abundant, as $k = 2$ strictly beats both for every
$\varepsilon > 0$. -/
@[category test, AMS 11]
theorem not_isColossallyAbundant_three_and_five :
    ¬ IsColossallyAbundant 3 ∧ ¬ IsColossallyAbundant 5 :=
  ⟨not_isColossallyAbundant_of_two_mul_sigma_le (by decide) (by decide),
    not_isColossallyAbundant_of_two_mul_sigma_le (by decide) (by decide)⟩

/-- Any adjacent pair `AreConsecutiveColossallyAbundant m n` satisfies $2 \le m < n$ and
$n \notin \{3, 5\}$. -/
@[category API, AMS 11]
theorem areConsecutiveColossallyAbundant_bounds {m n : ℕ}
    (h : AreConsecutiveColossallyAbundant m n) :
    2 ≤ m ∧ m + 1 ≤ n ∧ n ≠ 3 ∧ n ≠ 5 := by
  rcases h with ⟨hmn, hm, hn, -⟩
  exact ⟨hm.1, by omega, fun h3 => not_isColossallyAbundant_three_and_five.1 (h3 ▸ hn),
    fun h5 => not_isColossallyAbundant_three_and_five.2 (h5 ▸ hn)⟩

/-- **Alaoglu–Erdős Prime-Ratio Conjecture** [AE44]: whenever $m < n$ satisfy
`AreConsecutiveColossallyAbundant m n`, $n = p m$ for some prime $p$. -/
@[category research open, AMS 11]
theorem alaoglu_erdos_colossally_abundant_prime_ratio_conjecture (m n : ℕ)
    (h : AreConsecutiveColossallyAbundant m n) :
    ∃ p : ℕ, p.Prime ∧ n = p * m := by
  sorry

/-- **Alaoglu–Erdős Rational Prime-Powers Conjecture** [AE44]: if $p \ne q$ are primes and
$x \in \mathbb{R}$ satisfies $p^x \in \mathbb{Q}$ and $q^x \in \mathbb{Q}$, then
$x \in \mathbb{Z}$. -/
@[category research open, AMS 11]
theorem alaoglu_erdos_prime_powers_rational_conjecture (p q : ℕ) (x : ℝ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hr₁ : ∃ r₁ : ℚ, (p : ℝ) ^ x = r₁) (hr₂ : ∃ r₂ : ℚ, (q : ℝ) ^ x = r₂) :
    ∃ k : ℤ, x = k := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- Infinitely many integers satisfy `IsColossallyAbundant` [AE44]. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/ChironTheCentaur/rh-lab-colossally-abundant/blob/1ec2a3dd49685aa06ad701aa75b5e879dc0396c1/CAInfiniteFC/Main.lean#L179"]
theorem infinite_colossallyAbundant :
    {n : ℕ | IsColossallyAbundant n}.Infinite := by
  sorry

/-- Unconditional prime-or-squarefree-semiprime ratio theorem [AE44, p. 455]: if $m < n$ satisfy
`AreConsecutiveAlaogluErdosColossallyAbundant m n`, then $n / m$ is either prime or a product of two
distinct primes (proved via the six exponentials theorem [La66, Ra68]). Varying $\varepsilon > 0$
yields the same set of integers under `IsAlaogluErdosColossallyAbundant` as under [AE44, p. 448]'s
greatest-maximizer convention, so both give the same consecutive pairs; some one-sided strict
tie-breaker is needed, since a four-way tie $n, np, nq, npq$ with primes $p < q$ under two-sided
non-strict `IsColossallyAbundant` would include consecutive terms $np, nq$ of ratio $q / p$. -/
@[category research solved, AMS 11]
theorem alaoglu_erdos_prime_or_semiprime_ratio (m n : ℕ)
    (h : AreConsecutiveAlaogluErdosColossallyAbundant m n) :
    (∃ p : ℕ, p.Prime ∧ n = p * m) ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q * m := by
  sorry

/-- By the six exponentials theorem [La66, Ra68], for each $\varepsilon > 0$, at most four integers
$n > 1$ simultaneously maximize $\sigma_1(n) / n^{1+\varepsilon}$ [AE44, EN75]. -/
@[category research solved, AMS 11]
theorem encard_colossallyAbundant_maximizers_le_four (ε : ℝ) (hε : 0 < ε) :
    Set.encard {n : ℕ | 1 < n ∧ ∀ k : ℕ, 1 < k →
      (σ 1 k : ℝ) / (k : ℝ) ^ (1 + ε) ≤ (σ 1 n : ℝ) / (n : ℝ) ^ (1 + ε)} ≤ 4 := by
  sorry

end ColossallyAbundantNumber
