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

-- Erdos Problems URL: https://www.erdosproblems.com/418
import FormalConjectures.Util.ProblemImports

open scoped ArithmeticFunction

/--
Are there infinitely many integers not of the form $n - \phi(n)$?
-/
@[problem_status solved]
theorem erdos_418 :
    { (n - n.totient : ℕ) | n }ᶜ |>.Infinite :=
  sorry

/--
It follows from the Goldbach conjecture that every odd number can be
written as $n - \phi(n)$.
-/
@[problem_status solved]
theorem erdos_418.variants.conditional
    (goldbach : ∀ (n : ℕ) (hn : 2 < n),
      ∃ p q, Prime p ∧ Prime q ∧ n = p + q)
    (m : ℕ)
    (h : Odd m) :
    ∃ n, m + n.totient = n :=
  sorry

/--
Erdős has shown that a positive density set of integers cannot be written as
$\sigma(n) - n$.

[Er73b] Erdős, P., _Über die Zahlen der Form $\sigma (n)-n$ und $n-\phi(n)$_. Elem. Math. (1973), 83-86.
-/
@[problem_status solved]
theorem erdos_418.variants.sigma :
    ∃ (S : Set ℕ) (hS : ∀ α, S.HasDensity α → 0 < α),
      S ⊆ { (σ 1 n - n : ℕ) | n }ᶜ :=
  sorry

/--
A solution to erdos_418 was shown by Browkin and Schinzel [BrSc95] by
showing that any integer of the form $2^k\cdot 509203$ is not of the
form $n - \phi(n)$.

[BrSc95] Browkin, J. and Schinzel, A., _On integers not of the form {$n-\phi(n)$}_. Colloq. Math. (1995), 55-58.
-/
@[problem_status solved]
theorem erdos_418.variants.soln :
    { 2 ^ k * 509203 | k } ⊆ { (n - n.totient : ℕ) | n }ᶜ :=
  sorry

/--
It seems to be open whether there is a positive density set of integers
not of the form $n - \phi(n)$.
-/
@[problem_status open]
theorem erdos_418.variants.density :
    ∃ (S : Set ℕ) (hS : ∀ α, S.HasDensity α → 0 < α),
      S ⊆ { (n - n.totient : ℕ) | n }ᶜ :=
  sorry
