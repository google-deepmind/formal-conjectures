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
# Green's Open Problem 64

*Reference:* [Ben Green's Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.64)

Do there exist infinitely many primes $p$ for which $p - 2$ has an odd number of prime factors,
counted with multiplicity?
-/

open ArithmeticFunction

open scoped ArithmeticFunction.Omega

namespace Green64

/--
Do there exist infinitely many primes $p$ for which $p - 2$ has an odd number of prime factors,
counted with multiplicity (i.e. $\Omega(p - 2)$ is odd)?
-/
@[category research open, AMS 11]
theorem green_64 :
    answer(sorry) ↔ {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))}.Infinite := by
  sorry

/-- $5$ satisfies the condition: $5$ is prime and $5 - 2 = 3$ is prime, so $\Omega(3) = 1$ is odd. -/
@[category test, AMS 11]
theorem green_64_mem_five : 5 ∈ {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))} := by
  refine ⟨by norm_num, ?_⟩
  rw [show (5 : ℕ) - 2 = 3 by norm_num, cardFactors_apply_prime (by norm_num)]
  exact odd_one

/-- $7$ satisfies the condition: $7$ is prime and $7 - 2 = 5$ is prime, so $\Omega(5) = 1$ is odd. -/
@[category test, AMS 11]
theorem green_64_mem_seven : 7 ∈ {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))} := by
  refine ⟨by norm_num, ?_⟩
  rw [show (7 : ℕ) - 2 = 5 by norm_num, cardFactors_apply_prime (by norm_num)]
  exact odd_one

/-- $11$ does *not* satisfy the condition: although $11$ is prime, $11 - 2 = 9 = 3 ^ 2$ has
$\Omega(9) = 2$ prime factors, which is even. This shows the condition is non-trivial. -/
@[category test, AMS 11]
theorem green_64_not_mem_eleven : 11 ∉ {p : ℕ | p.Prime ∧ Odd (Ω (p - 2))} := by
  rintro ⟨-, hodd⟩
  rw [show (11 : ℕ) - 2 = 3 ^ 2 by norm_num, cardFactors_apply_prime_pow (by norm_num)] at hodd
  exact (by decide : ¬ Odd 2) hodd

/--
The same question as `green_64` but with $p - 1$ instead of $p - 2$.
Green notes this is "probably more natural".
-/
@[category research open, AMS 11]
theorem green_64.variants.p_sub_one :
    answer(sorry) ↔ {p : ℕ | p.Prime ∧ Odd (Ω (p - 1))}.Infinite := by
  sorry

end Green64
