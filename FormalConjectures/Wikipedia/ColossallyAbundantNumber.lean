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

An integer $n > 1$ is *colossally abundant* ([OEIS A004490](https://oeis.org/A004490):
$2, 6, 12, 60, 120, 360, \dots$) if some $\varepsilon > 0$ satisfies
$\sigma_1(n) / n^{1+\varepsilon} \ge \sigma_1(k) / k^{1+\varepsilon}$ for every $k > 1$. Alaoglu
and Erdős [AE44] predicted in 1944 that successive terms always differ by a prime factor, reducing
this claim to showing that $p^x, q^x \in \mathbb{Q}$ with distinct primes $p \ne q$ forces
$x \in \mathbb{Z}$ (cf. `Exponentials.four_exponentials_conjecture`). Combined with the
six-exponentials theorem of Lang and Ramachandra, [AE44] implies unconditionally that each
consecutive ratio is prime or squarefree semiprime and at most four integers $n > 1$ share any
given maximizer exponent $\varepsilon > 0$ (studied further by Erdős and Nicolas [EN75]).

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Colossally_abundant_number)
- [AE44] L. Alaoglu and P. Erdős (1944), Trans. Amer. Math. Soc. **56**, 448–469.
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

/-- Infinitely many integers satisfy `IsColossallyAbundant` [AE44]. -/
@[category research solved, AMS 11]
theorem infinite_colossallyAbundant :
    {n : ℕ | IsColossallyAbundant n}.Infinite := by
  sorry

/-- Unconditional prime-or-squarefree-semiprime ratio theorem [AE44]: if $m < n$ satisfy
`AreConsecutiveColossallyAbundant m n`, then $n / m$ is either prime or a product of two distinct
primes. -/
@[category research solved, AMS 11]
theorem alaoglu_erdos_prime_or_semiprime_ratio (m n : ℕ)
    (h : AreConsecutiveColossallyAbundant m n) :
    (∃ p : ℕ, p.Prime ∧ n = p * m) ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q * m := by
  sorry

/-- For each $\varepsilon > 0$, at most four integers $n > 1$ simultaneously maximize
$\sigma_1(n) / n^{1+\varepsilon}$ [AE44, EN75]. -/
@[category research solved, AMS 11]
theorem encard_colossallyAbundant_maximizers_le_four (ε : ℝ) (hε : 0 < ε) :
    Set.encard {n : ℕ | 1 < n ∧ ∀ k : ℕ, 1 < k →
      (σ 1 k : ℝ) / (k : ℝ) ^ (1 + ε) ≤ (σ 1 n : ℝ) / (n : ℝ) ^ (1 + ε)} ≤ 4 := by
  sorry

end ColossallyAbundantNumber
