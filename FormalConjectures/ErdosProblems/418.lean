/-
Copyright 2025 Google LLC

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
# Erdős Problem 418

*Reference:* [erdosproblems.com/418](https://www.erdosproblems.com/418)

Reviewed by @b-mehta on 2025-05-27
-/
open scoped ArithmeticFunction

/--
Are there infinitely many integers not of the form $n - \phi(n)$?

This is true, as shown by Browkin and Schinzel [BrSc95].

[BrSc95] Browkin, J. and Schinzel, A., _On integers not of the form {$n-\phi(n)$}_.
Colloq. Math. (1995), 55-58.
-/
@[category research solved, AMS 11]
theorem erdos_418 : { (n - n.totient : ℕ) | n }ᶜ.Infinite ↔ answer(True) :=
  sorry

/--
It follows from the Goldbach conjecture that every odd number can be
written as $n - \phi(n)$.
-/
@[category research solved, AMS 11]
theorem erdos_418.variants.conditional
    (goldbach : ∀ (n : ℕ), 2 < n → Even n → ∃ p q, Prime p ∧ Prime q ∧ n = p + q)
    (m : ℕ) (h : Odd m) :
    ∃ n, m + n.totient = n := by
  sorry

/--
Erdős has shown that a positive density set of integers cannot be written as
$\sigma(n) - n$.

[Er73b] Erdős, P., _Über die Zahlen der Form $\sigma (n)-n$ und $n-\phi(n)$_. Elem. Math. (1973), 83-86.
-/
@[category research solved, AMS 11]
theorem erdos_418.variants.sigma :
    ∃ (S : Set ℕ) (hS : S.HasPosDensity),
      S ⊆ { (σ 1 n - n : ℕ) | n }ᶜ :=
  sorry

/--
A solution to erdos_418 was shown by Browkin and Schinzel [BrSc95] by
showing that any integer of the form $2^(k + 1)\cdot 509203$ is not of the
form $n - \phi(n)$.

[BrSc95] Browkin, J. and Schinzel, A., _On integers not of the form {$n-\phi(n)$}_. Colloq. Math. (1995), 55-58.
-/
@[category research solved, AMS 11]
theorem erdos_418.variants.soln :
    { 2 ^ (k + 1) * 509203 | k } ⊆ { (n - n.totient : ℕ) | n }ᶜ :=
  sorry

/--
It seems to be open whether there is a positive density set of integers
not of the form $n - \phi(n)$.
-/
@[category research open, AMS 11]
theorem erdos_418.variants.density :
    (∃ (S : Set ℕ) (hS : S.HasPosDensity), S ⊆ { (n - n.totient : ℕ) | n }ᶜ) ↔ answer(sorry) :=
  sorry
