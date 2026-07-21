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
# Difference between first odd semiprime > 2^n and 2^n

Difference between first odd semiprime > 2^n and 2^n.

*References:*
- [A114137](https://oeis.org/A114137)
-/

namespace OeisA114137

/--
A natural number $n$ is a semiprime if it has exactly two prime factors counting multiplicity, $\Omega(n)=2$.
In Lean, `n.primeFactorsList.length` computes $\Omega(n)$.
-/
def is_semiprime (n : ℕ) : Prop :=
  n > 1 ∧ n.primeFactorsList.length = 2

/--
An odd semiprime is a semiprime that is odd.
-/
def is_odd_semiprime (n : ℕ) : Prop :=
  is_semiprime n ∧ Odd n

/--
The primary defining sequence `a`.
a(n) is the difference between first odd semiprime > 2^n and 2^n.
$$a(n) = \min \{s \mid s > 2^n \text{ and } s \text{ is an odd semiprime}\} - 2^n$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  let m := 2^n
  let S : Set ℕ := { s | s > m ∧ is_odd_semiprime s }
  sInf S - m

/--
In this powers of 2 sequence, does 1 occur infinitely often?
-/
@[category research open, AMS 11]
theorem conjecture1 :
  answer(sorry) ↔ Set.Infinite {n : ℕ | a n = 1} := by
  sorry

/--
Does every odd number occur?
-/
@[category research open, AMS 11]
theorem conjecture2 :
  answer(sorry) ↔ ∀ k : ℕ, Odd k → ∃ n : ℕ, a n = k := by
  sorry

end OeisA114137
