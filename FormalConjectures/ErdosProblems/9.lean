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
# Erdős Problem 9

*Reference:* [erdosproblems.com/9](https://www.erdosproblems.com/9)
-/

/--
The set of odd numbers that cannot be expressed as a prime plus two powers of 2.
-/
def Erdos9A : Set ℕ := { n | Odd n ∧ ¬ ∃ (p k l : ℕ), (Nat.Prime p) ∧ n = p + 2 ^ k + 2 ^ l }

/--
The set is known to be infinite. Erdős [Er77c] credits Schinzel with proving that there are
infinitely many odd integers not of this form, but gives no reference. Crocker [Cr71] has proved
there are are $\gg \log \log N$ such integers in $\{1, \dots, N\}$.
Pan [Pa11] improved this to $\gg_\epsilon N^{1 - \epsilon}$ for any $\epsilon > 0$.

Refs:
- [Er77c] Erdős, P., _Problems and results on combinatorial number theory. III._.
- [Cr71] Crocker, R., _On the sum of a prime and of two powers of two_.
- [Pa11] Pan, H., _On the integers not of the form {$p+2^a+2^b$}_.
-/
theorem erdos_9_infinite : Erdos9A.Infinite := by
  sorry

/--
Is the upper density of the set of odd numbers that cannot be expressed as a prime plus
two powers of 2 positive?
-/
@[category research open, AMS 5 11]
theorem erdos_9 : 0 < Erdos9A.upperDensity ↔ answer(sorry) := by
  sorry
