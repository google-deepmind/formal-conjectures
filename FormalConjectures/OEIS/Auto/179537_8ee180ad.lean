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

import FormalConjectures.Util.ProblemImports

open Finset Nat Int

/--
A179537: The sequence
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n-k}{k}^2 (-16)^k$$
-/
def A179537 (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    ((choose n k : ℤ) ^ 2) * ((choose (n - k) k : ℤ) ^ 2) * ((-16 : ℤ) ^ k)

theorem a_zero : A179537 0 = 1 := by sorry
theorem a_one : A179537 1 = 1 := by sorry
theorem a_two : A179537 2 = -63 := by sorry
theorem a_three : A179537 3 = -575 := by sorry

/-- The sum $\sum_{k=0}^{p-1} (-1)^k \cdot \text{A179537}(k)$ -/
def A179537_sum_unweighted (p : ℕ) : ℤ :=
  (Finset.range p).sum fun k : ℕ => ((-1 : ℤ) ^ k) * (A179537 k)

-- Definition of the auxiliary sum for the latter parts of Sun's conjecture
def A179537_sum_weighted (n : ℕ) : ℤ :=
  (Finset.range n).sum fun k : ℕ =>
    (((42 : ℤ) * Int.ofNat k + (37 : ℤ)) * ((-1 : ℤ) ^ k) * (A179537 k))

-- Legendre symbol $\left(\frac{\cdot}{7}\right)$
noncomputable def leg_sym_7 (p : ℕ) [h_prime : Fact p.Prime] : ℤ :=
  legendreSym p 7

/--
OEIS A179537 Conjecture 0 (Zhi-Wei Sun).
If $p$ is a prime with $(\frac{p}{7})=1$ and $p=x^2+7y^2$ with $x,y$ integers, then $\sum_{k=0}^{p-1}(-1)^k a(k)=4x^2-2p \pmod{p^2}$;
if $p$ is a prime with $(\frac{p}{7})=-1$, then $\sum_{k=0}^{p-1}(-1)^k a(k)=0 \pmod{p^2}$.
-/
theorem oeis_179537_conjecture_sun_part1 (p : ℕ) [h_prime : Fact p.Prime] (h_p_ne_7 : p ≠ 7) :
  (leg_sym_7 p = 1 →
    -- The existence of x, y is a known equivalence for primes $p \equiv 1, 2, 4 \pmod 7$.
    -- We formalize the combined modular statement.
    ∃ (x y : ℤ), ((p : ℤ) = x^2 + 7 * y^2 ∧
      A179537_sum_unweighted p ≡ 4 * x^2 - 2 * (p : ℤ) [ZMOD (p : ℤ) ^ 2])) ∧
  (leg_sym_7 p = -1 →
    A179537_sum_unweighted p ≡ 0 [ZMOD (p : ℤ) ^ 2]) := by sorry

/--
OEIS A179537 Conjecture 0 (Zhi-Wei Sun). Part 2a: Modulo $n$ congruence for the weighted sum.
$$ \sum_{k=0}^{n-1}(42k+37)(-1)^k a(k) \equiv 0 \pmod n $$
for all $n \ge 1$.
-/
theorem oeis_179537_conjecture_sun_part2a_mod_n :
  ∀ n : ℕ, n ≥ 1 → A179537_sum_weighted n ≡ 0 [ZMOD n] := by sorry

/--
OEIS A179537 Conjecture 0 (Zhi-Wei Sun). Part 2b: Modulo $p^2$ congruence for the weighted sum.
$$ \sum_{k=0}^{p-1}(42k+37)(-1)^k a(k) \equiv p(21(p/7)+16) \pmod{p^2} $$
for any prime $p \ne 7$.
-/
theorem oeis_179537_conjecture_sun_part2b_mod_p_sq (p : ℕ) [h_prime : Fact p.Prime] (h_p_ne_7 : p ≠ 7) :
  A179537_sum_weighted p ≡
    (p : ℤ) * (((21 : ℤ) * leg_sym_7 p) + (16 : ℤ)) [ZMOD (p : ℤ) ^ 2] := by sorry
