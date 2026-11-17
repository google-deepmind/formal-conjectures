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
# Squarefreeness of Prime-Index Mersenne Numbers

Write $M_n = 2^n - 1$ (`mersenne n`) for $n \in \mathbb{N}$. Composite exponents admit repeated
prime factors—for instance $M_6 = 63 = 3^2 \cdot 7$—whereas whether $M_q = 2^q - 1$ is squarefree
at every prime exponent $q$ remains an open problem. Any prime divisor $p \mid M_q$ with $q$ prime
satisfies $p^2 \mid M_q$ precisely when `IsWieferichPrime p` holds, and Andrzej Rotkiewicz (1965)
proved that infinitely many squarefree values $M_n$ imply that infinitely many primes fail
`IsWieferichPrime`.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Prime_numbers)
- [Wikipedia: Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime)
- A. Rotkiewicz, *Sur les nombres de Mersenne dépourvus de diviseurs carrés et sur les nombres
  naturels $n$, tels que $n^2 \mid 2^n - 2$*, Mat. Vesnik **2** (17) (1965), 78–80.
-/

@[expose] public section

namespace SquarefreeMersenne

/-- Checks `Squarefree (mersenne p)` at $p = 2, 3$ and at the first composite prime-exponent value
$M_{11} = 2047 = 23 \cdot 89$. -/
@[category test, AMS 11]
theorem squarefree_mersenne_small_primes :
    Squarefree (mersenne 2) ∧ Squarefree (mersenne 3) ∧ Squarefree (mersenne 11) := by
  decide +kernel

/-- Confirms that $M_0 = 0$ and $M_6 = 63 = 3^2 \cdot 7$ fail `Squarefree`, motivating the
restriction to prime exponents. -/
@[category test, AMS 11]
theorem not_squarefree_mersenne_zero_and_six :
    ¬ Squarefree (mersenne 0) ∧ ¬ Squarefree (mersenne 6) := by
  refine ⟨by rw [mersenne_zero]; exact not_squarefree_zero, fun h => ?_⟩
  have h3 : IsUnit (3 : ℕ) := h 3 ⟨7, rfl⟩
  rw [Nat.isUnit_iff] at h3
  omega

/-- At composite exponent $q = 6$, $3^2 \mid M_6 = 63$ even though $3$ is not a Wieferich prime. -/
@[category test, AMS 11]
theorem composite_index_sq_dvd_not_wieferich :
    3 ^ 2 ∣ mersenne 6 ∧ ¬ IsWieferichPrime 3 :=
  ⟨⟨7, rfl⟩, by decide⟩

/--
Is $M_p = 2^p - 1$ squarefree for every prime $p$?
-/
@[category research open, question, AMS 11]
theorem squarefree_mersenne_of_prime :
    ∀ p : ℕ, p.Prime → Squarefree (mersenne p) := by
  sorry

/--
For primes $q$ and $p$ with $p \mid M_q$, the square $p^2$ divides $M_q = 2^q - 1$ precisely when
`IsWieferichPrime p` holds.
-/
@[category textbook, AMS 11]
theorem sq_dvd_mersenne_iff_isWieferichPrime
    {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hdvd : p ∣ mersenne q) :
    p ^ 2 ∣ mersenne q ↔ IsWieferichPrime p := by
  sorry

/--
Rotkiewicz's theorem (1965): if infinitely many values $M_n = 2^n - 1$ are squarefree, then
infinitely many primes fail `IsWieferichPrime`.
-/
@[category research solved, AMS 11]
theorem rotkiewicz_infinite_non_wieferich_of_squarefree_mersenne :
    {n : ℕ | Squarefree (mersenne n)}.Infinite →
      {p : ℕ | p.Prime ∧ ¬ IsWieferichPrime p}.Infinite := by
  sorry

end SquarefreeMersenne
