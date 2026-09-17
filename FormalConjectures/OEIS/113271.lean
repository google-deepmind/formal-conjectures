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

import FormalConjecturesUtil

/-!
# Ascending descending base exponent transform of $2^n$

*References:*
- [A113271](https://oeis.org/A113271)
-/

namespace OeisA113271

/--
The primary defining sequence `a`.
$a(n)$ is the ascending descending base exponent transform of $2^n$.
$$a(n) = \sum_{i=0}^n 2^{i \cdot 2^{n-i}}$$
-/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), 2 ^ (i * 2 ^ (n - i))

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 9 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 41 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 593 := by rfl

@[category test, AMS 11]
theorem a_4_prime : (a 4).Prime := by
  rw [a_4]
  norm_num

/-- The next term from the defining formula and the official OEIS b-file. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 135457 := by rfl

/-- The term `a(5) = 135457 = 7 * 37 * 523` is composite. -/
@[category test, AMS 11]
theorem a_5_not_prime : ¬ (a 5).Prime := by
  rw [a_5]
  norm_num

/--
The first prime terms in this (always odd) sequence are $a(1) = 3$, $a(3) = 41$, and
$a(4) = 593$. What is the next prime?

The OEIS comment currently says `$a(5) = 543$`, but this conflicts with its defining formula,
b-file, and examples: the actual index-five term is the composite number `135457`. Consequently the
search for the next prime must begin after index `4`, not after index `5`.
-/
@[category research open, AMS 11]
theorem conjecture1 :
  answer(sorry) = a (sInf {n : ℕ | 4 < n ∧ (a n).Prime}) := by
  sorry

end OeisA113271
