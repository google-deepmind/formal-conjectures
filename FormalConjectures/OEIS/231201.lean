/-
Copyright 2025 The Formal Conjectures Authors.

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
# Sum of two numbers with prime conditions

Number of ways to write $n = x+y$, for $x,y > 0$ such that  $2^x + y$ is prime.

Zhi-Wei Sun has offered a $1000 prize for the first proof.

*References:*
- [OEIS A231201](https://oeis.org/A231201)
- Zhi-Wei Sun, "Table of n, a(n) for n = 1..10000",
  "Write n = k + m with 2^k + m prime", a message to Number Theory List, Nov. 16, 2013,
  "On a^n+ bn modulo m", arXiv:1312.1166 [math.NT], 2013-2014,
  "Problems on combinatorial properties of primes", arXiv:1402.6641 [math.NT], 2014-2015.
-/

namespace OeisA231201

/-- The predicate that `n` can be written as $x + y$ with $x,y >0$ such that
$2^x + y$ is prime -/
def PrimeCondition (n: ℕ) : Prop :=
  ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧ (2^x + y).Prime

@[category test, AMS 11]
theorem PrimeCondition_8 : PrimeCondition 8 :=
  ⟨3, 5, by norm_num, by norm_num, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem PrimeCondition_53 : PrimeCondition 53 :=
  ⟨20, 33, by norm_num, by norm_num, by norm_num, by norm_num⟩

@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 < n) : PrimeCondition n := by
  sorry

end OeisA231201
