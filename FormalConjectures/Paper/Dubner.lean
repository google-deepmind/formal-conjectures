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
# Dubner's conjecture

*Reference*: [Every even number greater than 4208 is the sum of two t-primes](https://scispace.com/pdf/twin-prime-conjectures-3icaxy6b0m.pdf)
by *Harvey Dubner*.
-/

namespace DubnerConjecture

/--
A twin prime is a prime number that has a prime gap of 2, meaning either p - 2 or p + 2
is also prime.
-/
def IsTwinPrime (p : ℕ) : Prop :=
  p.Prime ∧ ((p - 2).Prime ∨ (p + 2).Prime)

@[category test, AMS 11]
theorem t1 : ¬IsTwinPrime 2 := by
  norm_num [IsTwinPrime]

@[category test, AMS 11]
theorem t2 : IsTwinPrime 3 := by
  norm_num [IsTwinPrime]

@[category test, AMS 11]
theorem t3 : IsTwinPrime 5 := by
  norm_num [IsTwinPrime]

@[category test, AMS 11]
theorem t4 : IsTwinPrime 101 := by
  norm_num [IsTwinPrime]

@[category test, AMS 11]
theorem t5 : ¬IsTwinPrime 100 := by
  norm_num [IsTwinPrime]

/--
Every even number greater than 4208 is the sum of two twin primes.
-/
@[category research open, AMS 11]
theorem dubner_conjecture (n : ℕ) (hn : 4208 < n) (h : Even n) :
    ∃ p q : ℕ,
      IsTwinPrime p ∧
      IsTwinPrime q ∧
      p + q = n := by
  sorry

end DubnerConjecture
