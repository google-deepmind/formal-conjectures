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

/-!
# Fortune's Conjecture

A *Fortunate number* is the smallest integer $m > 1$ such that $p_n\# + m$ is prime,
where $p_n\#$ denotes the primorial of the $n$-th prime — equivalently, the product
of the first $n$ primes.

**Fortune's Conjecture** asserts that every Fortunate number is prime — equivalently,
that no Fortunate number is composite.

The conjecture is named after the social anthropologist Reo Fortune, who proposed it.
The first few Fortunate numbers are $3, 5, 7, 13, 23, 17, 19, 23, 37, 61, \ldots$
(OEIS A005235); all known values are prime.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Fortunate_number)
- [OEIS A005235](https://oeis.org/A005235)
- [PrimePages glossary entry](https://primes.utm.edu/glossary/xpage/FortunateNumber.html)
- [PlanetMath: Fortune's conjecture](https://planetmath.org/fortunesconjecture)
-/

namespace FortuneConjecture

open Nat

/-- For any natural number `N` there is some `m > 1` with `N + m` prime; an
immediate consequence of the infinitude of primes. -/
@[category API, AMS 11]
lemma exists_one_lt_prime_add (N : ℕ) : ∃ m, 1 < m ∧ Nat.Prime (N + m) := by
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (N + 2)
  refine ⟨p - N, by omega, ?_⟩
  have hsum : N + (p - N) = p := by omega
  rw [hsum]; exact hp_prime

/-- The $n$-th *Fortunate number* (0-indexed): the smallest integer $m > 1$ such
that $p_{n+1}\# + m$ is prime.

`Nat.nth Nat.Prime n` is the $(n+1)$-st prime (0-indexed), and `primorial p` is the
product of all primes $\le p$; when $p$ is the $(n+1)$-st prime this equals the
product of the first $n+1$ primes. Thus `fortunateNumber 0` corresponds to
$F_1 = 3$ in the OEIS A005235 indexing. -/
noncomputable def fortunateNumber (n : ℕ) : ℕ :=
  Nat.find (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime n)))

/-- `fortunateNumber n` is greater than $1$, and adding it to the primorial of
the $(n+1)$-st prime yields a prime. -/
@[category API, AMS 11]
lemma fortunateNumber_spec (n : ℕ) :
    1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) :=
  Nat.find_spec (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime n)))

/-- Minimality of `fortunateNumber n`: no smaller integer $m > 1$ makes
`primorial (Nat.nth Nat.Prime n) + m` prime. -/
@[category API, AMS 11]
lemma fortunateNumber_le (n m : ℕ) (hm : 1 < m)
    (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    fortunateNumber n ≤ m :=
  Nat.find_min' (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime n))) ⟨hm, hp⟩

-- The first four Fortunate numbers (OEIS A005235): 3, 5, 7, 13.

@[category API, AMS 11]
theorem fortunateNumber_zero : fortunateNumber 0 = 3 := by
  have hp : primorial (Nat.nth Nat.Prime 0) = 2 := by
    rw [Nat.nth_prime_zero_eq_two]; decide
  show Nat.find (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime 0))) = 3
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, ?_⟩, ?_⟩
  · show Nat.Prime (primorial (Nat.nth Nat.Prime 0) + 3)
    rw [hp]; norm_num
  · rintro m hm ⟨hm1, hmp⟩
    rw [hp] at hmp
    interval_cases m
    norm_num at hmp

@[category API, AMS 11]
theorem fortunateNumber_one : fortunateNumber 1 = 5 := by
  have hp : primorial (Nat.nth Nat.Prime 1) = 6 := by
    rw [Nat.nth_prime_one_eq_three]; decide
  show Nat.find (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime 1))) = 5
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, ?_⟩, ?_⟩
  · show Nat.Prime (primorial (Nat.nth Nat.Prime 1) + 5)
    rw [hp]; norm_num
  · rintro m hm ⟨hm1, hmp⟩
    rw [hp] at hmp
    interval_cases m <;> norm_num at hmp

@[category API, AMS 11]
theorem fortunateNumber_two : fortunateNumber 2 = 7 := by
  have hp : primorial (Nat.nth Nat.Prime 2) = 30 := by
    rw [Nat.nth_prime_two_eq_five]; decide
  show Nat.find (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime 2))) = 7
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, ?_⟩, ?_⟩
  · show Nat.Prime (primorial (Nat.nth Nat.Prime 2) + 7)
    rw [hp]; norm_num
  · rintro m hm ⟨hm1, hmp⟩
    rw [hp] at hmp
    interval_cases m <;> norm_num at hmp

@[category API, AMS 11]
theorem fortunateNumber_three : fortunateNumber 3 = 13 := by
  have hp : primorial (Nat.nth Nat.Prime 3) = 210 := by
    rw [Nat.nth_prime_three_eq_seven]; decide
  show Nat.find (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime 3))) = 13
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, ?_⟩, ?_⟩
  · show Nat.Prime (primorial (Nat.nth Nat.Prime 3) + 13)
    rw [hp]; norm_num
  · rintro m hm ⟨hm1, hmp⟩
    rw [hp] at hmp
    interval_cases m <;> norm_num at hmp

/-- **Fortune's Conjecture**: Every Fortunate number is prime. -/
@[category research open, AMS 11]
theorem fortune_conjecture :
    answer(sorry) ↔ (∀ n : ℕ, Nat.Prime (fortunateNumber n)) := by
  sorry

end FortuneConjecture

