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

/--
A generalized Cullen number in base $b \ge 2$ is a natural number of the form
$n \cdot b^n + 1$ with $n + 2 > b$.
-/
def IsGeneralizedCullenNumber (b c : ℕ) : Prop :=
  2 ≤ b ∧ ∃ n : ℕ, b < n + 2 ∧ c = n * b ^ n + 1

/--
A generalized Cullen prime in base $b \ge 2$ is a prime number that is a generalized Cullen
number in base $b$.
-/
def IsGeneralizedCullenPrime (b p : ℕ) : Prop :=
  p.Prime ∧ IsGeneralizedCullenNumber b p

/--
For every integer base $b \ge 2$, there are infinitely many generalized Cullen primes of base $b$.
-/
@[category research open, AMS 11]
theorem infinitely_many_generalized_cullen_primes :
    ∀ b ≥ 2, Set.Infinite {p : ℕ | IsGeneralizedCullenPrime b p} := by
  sorry

end CullenPrime
