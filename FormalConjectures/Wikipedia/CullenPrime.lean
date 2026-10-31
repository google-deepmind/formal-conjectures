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
# Cullen primes

A Cullen number is a natural number of the form $n \cdot 2^n + 1$, where $n$ is a
positive integer. A Cullen prime is a Cullen number that is prime. It is
conjectured that there are infinitely many Cullen primes.

*References:*
- [Wikipedia, Cullen number](https://en.wikipedia.org/wiki/Cullen_number)
- [OEIS A005849](https://oeis.org/A005849)
- [OEIS A050920](https://oeis.org/A050920)
-/

@[expose] public section

namespace CullenPrime

/-- A Cullen number is a natural number of the form $n \cdot 2^n + 1$ for $n \ge 1$. -/
def IsCullenNumber (c : ℕ) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ c = n * 2 ^ n + 1

/-- A Cullen prime is a prime number that is also a Cullen number. -/
def IsCullenPrime (p : ℕ) : Prop :=
  p.Prime ∧ IsCullenNumber p

@[category test, AMS 11]
theorem three_isCullenPrime : IsCullenPrime 3 := by
  refine ⟨by norm_num, 1, by norm_num, ?_⟩
  norm_num

/-- There are infinitely many Cullen primes. -/
@[category research open, AMS 11]
theorem infinitely_many_cullen_primes :
    Set.Infinite {p : ℕ | IsCullenPrime p} := by
  sorry

/--
There are infinitely many positive integers $n$ such that $n \cdot 2^n + 1$ is prime.
-/
@[category research open, AMS 11]
theorem infinitely_many_cullen_primes.variants.indices :
    Set.Infinite {n : ℕ | 1 ≤ n ∧ (n * 2 ^ n + 1).Prime} := by
  sorry

/--
The prime formulation and index formulation of the Cullen prime conjecture are equivalent.
-/
@[category research solved, AMS 11]
theorem infinitely_many_cullen_primes.variants.equivalence :
    Set.Infinite {p : ℕ | IsCullenPrime p} ↔
      Set.Infinite {n : ℕ | 1 ≤ n ∧ (n * 2 ^ n + 1).Prime} := by
  sorry

end CullenPrime
