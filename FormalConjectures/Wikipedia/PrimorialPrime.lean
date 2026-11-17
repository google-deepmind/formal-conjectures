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
# Infinitude of primorial primes

For $n \in \mathbb{N}$, let $p_n\#$ (`Nat.kthPrimorial n`) denote the primorial multiplying the
initial $n$ primes (with $p_0\# = 1$). Primes equal to $p_n\# + 1$ (Euclid primes, `OEIS A018239`)
or $p_n\# - 1$ (Kummer primes, `OEIS A057705`) are called *primorial primes* (`OEIS A228486`,
studied computationally by Dubner 1987). Although $p_n\# + 1$ always has a prime factor exceeding
$p_n$, the integers $p_n\# \pm 1$ are often composite (beginning with
$p_4\# - 1 = 209 = 11 \times 19$ and $p_6\# + 1 = 30031 = 59 \times 509$). Whether infinitely many
primorial primes exist, whether infinitely many Kummer primes exist, and whether infinitely many
numbers $p_n\# \pm 1$ are composite all remain open.

*References:*
- [Wikipedia: Primorial prime](https://en.wikipedia.org/wiki/Primorial_prime)
- [Wikipedia: Euclid number](https://en.wikipedia.org/wiki/Euclid_number#Unsolved_problems)
- [OEIS A228486](https://oeis.org/A228486)
- [OEIS A018239](https://oeis.org/A018239)
- [OEIS A057705](https://oeis.org/A057705)
- H. Dubner, *Factorial and primorial primes*, J. Recreational Math. **19** (1987), no. 3,
  197–203.
-/

@[expose] public section

namespace PrimorialPrime

/-- A prime equal to $p_n\# + 1$ for some $n \in \mathbb{N}$ (a Euclid primorial prime, including
$p_0\# + 1 = 2$). -/
def IsEuclidPrimorialPrime (q : ℕ) : Prop :=
  q.Prime ∧ ∃ n : ℕ, q = Nat.kthPrimorial n + 1

/-- A prime equal to $p_n\# - 1$ for some $n \in \mathbb{N}$ (a Kummer primorial prime). -/
def IsKummerPrimorialPrime (q : ℕ) : Prop :=
  q.Prime ∧ ∃ n : ℕ, q + 1 = Nat.kthPrimorial n

/-- A prime equal to $p_n\# \pm 1$ for some $n \in \mathbb{N}$. -/
def IsPrimorialPrime (q : ℕ) : Prop :=
  IsEuclidPrimorialPrime q ∨ IsKummerPrimorialPrime q

/-- Verifies $2 = p_0\# + 1$, $3 = p_1\# + 1$, and $31 = p_3\# + 1$ as Euclid primorial primes,
and $5 = p_2\# - 1$ and $29 = p_3\# - 1$ as Kummer primorial primes. -/
@[category test, AMS 11]
theorem primorialPrime_small_witnesses :
    IsEuclidPrimorialPrime 2 ∧ IsEuclidPrimorialPrime 3 ∧ IsEuclidPrimorialPrime 31 ∧
      IsKummerPrimorialPrime 5 ∧ IsPrimorialPrime 29 := by
  refine ⟨⟨by decide, 0, by simp⟩, ⟨by decide, 1, by simp⟩, ⟨by decide, 3, by simp⟩,
    ⟨by decide, 2, by simp⟩, Or.inr ⟨by decide, 3, by simp⟩⟩

/-- Checks that $p_4\# - 1 = 209 = 11 \times 19$ and $p_6\# + 1 = 30031 = 59 \times 509$ are
composite, hence not primorial primes. -/
@[category test, AMS 11]
theorem not_primorialPrime_counterexamples :
    ¬ IsPrimorialPrime (Nat.kthPrimorial 4 - 1) ∧ ¬ (Nat.kthPrimorial 6 + 1).Prime := by
  have h4 : Nat.kthPrimorial 4 = 210 := Nat.kthPrimorial_four
  have h6 : Nat.kthPrimorial 6 = 30030 := by
    rw [Nat.kthPrimorial_succ, Nat.kthPrimorial_five, Nat.nth_prime_five_eq_thirteen]
  rw [h4, h6]
  refine ⟨?_, by norm_num⟩
  rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> norm_num at hp

/-- Every primorial prime is prime, and infinitude of either Euclid or Kummer primorial primes
implies infinitude of `IsPrimorialPrime`. -/
@[category API, AMS 11]
theorem isPrimorialPrime_prime_and_infinite_imp :
    (∀ q : ℕ, IsPrimorialPrime q → q.Prime) ∧
      ({q : ℕ | IsEuclidPrimorialPrime q}.Infinite → {q : ℕ | IsPrimorialPrime q}.Infinite) ∧
      ({q : ℕ | IsKummerPrimorialPrime q}.Infinite → {q : ℕ | IsPrimorialPrime q}.Infinite) := by
  refine ⟨?_, fun h => h.mono fun _ hq => Or.inl hq, fun h => h.mono fun _ hq => Or.inr hq⟩
  rintro q (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq

/-- Verifies $7 = p_2\# + 1$ and $211 = p_4\# + 1$ as Euclid primorial primes, and
$2309 = p_5\# - 1$ as a Kummer primorial prime. -/
@[category test, AMS 11]
theorem primorialPrime_three_seven_eleven :
    IsEuclidPrimorialPrime 7 ∧ IsEuclidPrimorialPrime 211 ∧ IsKummerPrimorialPrime 2309 := by
  refine ⟨⟨by decide, 2, by simp⟩, ⟨by norm_num, 4, by simp⟩, ⟨by norm_num, 5, by simp⟩⟩

/-- Do infinitely many primorial primes $p_n\# \pm 1$ exist? (The positive-sign case $p_n\# + 1$
appears as `EuclidNumbers.infinite_prime_euclid_numbers`.) -/
@[category research open, question, AMS 11]
theorem infinitely_many_primorial_primes :
    {q : ℕ | IsPrimorialPrime q}.Infinite := by
  sorry

/-- Do infinitely many Kummer primes $p_n\# - 1$ exist? -/
@[category research open, question, AMS 11]
theorem infinitely_many_primorial_primes.variants.kummer :
    {q : ℕ | IsKummerPrimorialPrime q}.Infinite := by
  sorry

/-- Are infinitely many integers of the form $p_n\# \pm 1$ composite? -/
@[category research open, question, AMS 11]
theorem infinitely_many_primorial_primes.variants.composite :
    {m : ℕ | m.Composite ∧
      ∃ n : ℕ, m = Nat.kthPrimorial n + 1 ∨ m + 1 = Nat.kthPrimorial n}.Infinite := by
  sorry

end PrimorialPrime
