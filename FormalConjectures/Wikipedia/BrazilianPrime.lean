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
# Infinitude of Brazilian primes

Introduced at Fortaleza in the 1994 Iberoamerican Mathematical Olympiad, an integer $n \ge 7$ is
*Brazilian* (`A125134`) when some radix $b$ ($2 \le b \le n - 2$) expresses $n$ using $k \ge 2$
equal digits $d \in \{1, \dots, b - 1\}$, i.e. $n = d (b^k - 1) / (b - 1)$. Any prime with this
property (`A085104`: $7, 13, 31, 43, 73, 127, \dots$) forces $d = 1$ and an odd prime length
$k = q \ge 3$, so $n = (b^q - 1) / (b - 1)$ is a repunit of odd prime length. Schott (2010)
established convergence of the reciprocal series over Brazilian primes (`A306759`), and elementary
counting yields relative natural density $0$ among all primes, while whether infinitely many
Brazilian primes exist remains open.

*References:*
- [Wikipedia: Brazilian number](https://en.wikipedia.org/wiki/Brazilian_number)
- [OEIS A125134](https://oeis.org/A125134)
- [OEIS A085104](https://oeis.org/A085104)
- [OEIS A306759](https://oeis.org/A306759)
- B. Schott, *Les nombres brésiliens*, Quadrature **76** (2010), 30–38.
-/

@[expose] public section

namespace BrazilianPrime

/-- An integer $n$ is *Brazilian* if in some radix $b$ ($2 \le b \le n - 2$) its expansion consists
of $k \ge 2$ copies of a digit $1 \le d < b$, i.e. $n (b - 1) = d (b^k - 1)$. -/
def IsBrazilian (n : ℕ) : Prop :=
  ∃ b d k : ℕ, 2 ≤ b ∧ b + 2 ≤ n ∧ 1 ≤ d ∧ d < b ∧ 2 ≤ k ∧ n * (b - 1) = d * (b ^ k - 1)

/-- $7 = 111_2$ satisfies `IsBrazilian` ($b = 2, d = 1, k = 3$). -/
@[category test, AMS 11]
theorem isBrazilian_seven : IsBrazilian 7 :=
  ⟨2, 1, 3, by omega, by omega, by omega, by omega, by omega, by norm_num⟩

/-- $13 = 111_3$ satisfies `IsBrazilian` ($b = 3, d = 1, k = 3$). -/
@[category test, AMS 11]
theorem isBrazilian_thirteen : IsBrazilian 13 :=
  ⟨3, 1, 3, by omega, by omega, by omega, by omega, by omega, by norm_num⟩

/-- No integer $n \le 6$ satisfies `IsBrazilian`, making $7$ the least Brazilian integer. -/
@[category test, AMS 11]
theorem not_isBrazilian_le_six {n : ℕ} (hn : n ≤ 6) : ¬ IsBrazilian n := by
  rintro ⟨b, d, k, hb2, hbn, hd1, hdb, hk2, heq⟩
  have hb4 : b ≤ 4 := by omega
  have hk3 : k ≤ 2 := Nat.le_of_not_lt fun hgt => by
    have hb3 : b ^ 3 ≤ b ^ k := Nat.pow_le_pow_right (by omega) hgt
    have hmul := Nat.mul_le_mul hd1 (Nat.sub_le_sub_right hb3 1)
    interval_cases b <;> omega
  have hk_eq : k = 2 := by omega
  subst hk_eq
  interval_cases b <;> omega

/--
**Schott's Theorem** (2010, Theorem 4): the reciprocal series $\sum 1 / p$ over Brazilian primes
converges in $\mathbb{R}$.
-/
@[category research solved, AMS 11]
theorem brazilian_primes_reciprocal_summable :
    Summable (fun p : {p : ℕ // p.Prime ∧ IsBrazilian p} => (1 : ℝ) / (p.1 : ℝ)) := by
  sorry

/--
Brazilian primes have relative natural density $0$ inside the primes.
-/
@[category textbook, AMS 11]
theorem brazilian_primes_zero_relative_density :
    {p : ℕ | p.Prime ∧ IsBrazilian p}.HasDensity 0 {p : ℕ | p.Prime} := by
  sorry

/--
Are infinitely many primes Brazilian?
-/
@[category research open, question, AMS 11]
theorem infinitely_many_brazilian_primes :
    {p : ℕ | p.Prime ∧ IsBrazilian p}.Infinite := by
  sorry

end BrazilianPrime
