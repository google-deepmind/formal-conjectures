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
# Proth primes

A *Proth number* is an integer $N = k \cdot 2^n + 1$ where $k$ is odd and $1 \le k < 2^n$. A Proth
number that is prime is called a *Proth prime*. Proth proved in 1878 that a Proth number $N$ is
prime if and only if $-1$ is an $((N - 1)/2)$-th power modulo $N$. It remains open whether
infinitely many Proth primes exist, and in particular whether any fixed odd multiplier such as
$k = 3$ produces infinitely many primes $3 \cdot 2^n + 1$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Proth_prime)
- [OEIS A080076](https://oeis.org/A080076)
- [OEIS A002253](https://oeis.org/A002253)
- [Pr1878] Proth, F. (1878). *Théorèmes sur les nombres premiers*, C. R. Acad. Sci. Paris 87, 926.
- [CP05] Crandall, R. and Pomerance, C. (2005). *Prime Numbers: A Computational Perspective*, 2nd
  ed., Springer, New York.
-/

@[expose] public section

namespace ProthPrime

/-- An integer $N$ is a **Proth number** if $N = k \cdot 2^n + 1$ for some odd $k$ and $n \ge 1$
with $k < 2^n$. -/
def IsProthNumber (N : ℕ) : Prop :=
  ∃ k n : ℕ, Odd k ∧ 1 ≤ n ∧ k < 2 ^ n ∧ N = k * 2 ^ n + 1

/-- A prime integer that is also a Proth number ([OEIS A080076](https://oeis.org/A080076)). -/
def IsProthPrime (N : ℕ) : Prop :=
  N.Prime ∧ IsProthNumber N

/-- $13 = 3 \cdot 2^2 + 1$ is a Proth prime. -/
@[category test, AMS 11]
theorem isProthPrime_thirteen : IsProthPrime 13 :=
  ⟨by decide, 3, 2, ⟨1, rfl⟩, by omega, by omega, by omega⟩

/-- $41 = 5 \cdot 2^3 + 1$ is a Proth prime. -/
@[category test, AMS 11]
theorem isProthPrime_forty_one : IsProthPrime 41 :=
  ⟨by decide, 5, 3, ⟨2, rfl⟩, by omega, by omega, by omega⟩

/-- $9 = 1 \cdot 2^3 + 1$ is a composite Proth number. -/
@[category test, AMS 11]
theorem isProthNumber_nine_and_not_prime : IsProthNumber 9 ∧ ¬ IsProthPrime 9 :=
  ⟨⟨1, 3, ⟨0, rfl⟩, by omega, by omega, by omega⟩, fun h => absurd h.1 (by decide)⟩

/-- $7 = 3 \cdot 2^1 + 1$ is prime, but is not a Proth number because $3 \not< 2^1$. -/
@[category test, AMS 11]
theorem not_isProthNumber_seven : ¬ IsProthNumber 7 := by
  rintro ⟨k, n, hk, _, _, heq⟩
  have hn_le : n ≤ 2 := by
    by_contra h
    have hpow : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    have hk1 : 1 ≤ k := hk.pos
    nlinarith
  interval_cases n <;> omega

/-- If an odd multiplier $k$ is a Sierpiński number (`Nat.IsSierpinskiNumber`), then
$k \cdot 2^n + 1$ is never prime for any $n \in \mathbb{N}$. -/
@[category API, AMS 11]
theorem not_prime_proth_of_isSierpinskiNumber {k : ℕ} (hk : k.IsSierpinskiNumber) (n : ℕ) :
    ¬ (k * 2 ^ n + 1).Prime :=
  (hk.2 n).2

/--
**Proth's primality theorem** [Pr1878, CP05]: a Proth number $N = k \cdot 2^n + 1$ ($k$ odd,
$k < 2^n$) is prime if and only if there exists $a \in \mathbb{Z}/N\mathbb{Z}$ with
$a^{(N - 1) / 2} = -1$.
-/
@[category research solved, AMS 11]
theorem proth_primality_criterion (N : ℕ) (hN : IsProthNumber N) :
    N.Prime ↔ ∃ a : ZMod N, a ^ ((N - 1) / 2) = -1 := by
  sorry

/--
There are infinitely many integers $n \ge 2$ such that $3 \cdot 2^n + 1$ is a Proth prime
([OEIS A002253](https://oeis.org/A002253)).

The bound $n \ge 2$ ensures $3 < 2^n$, so that $3 \cdot 2^n + 1$ is a Proth number.
-/
@[category research open, AMS 11]
theorem infinitely_many_proth_primes_multiplier_three :
    {n : ℕ | 2 ≤ n ∧ (3 * 2 ^ n + 1).Prime}.Infinite := by
  sorry

end ProthPrime
