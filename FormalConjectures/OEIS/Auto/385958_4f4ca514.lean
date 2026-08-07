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

open Nat Finset

/--
A helper function to find the largest prime $p$ such that $p-1$ divides $2 \cdot k$.
This is the definition of $a(n)$ given $b(n-1)=k$.
Since $k \ge 1$, $2k \ge 2$, and the set of such primes is non-empty (it always contains $p=2$).
-/
noncomputable def largest_prime_divisor_property (k : ℕ) : ℕ :=
  -- Generate candidates p = d + 1 where d is a divisor of 2k. Filter for primes and find the max.
  let candidates := Finset.image (fun d => d + 1) (2 * k).divisors
  let max_prime := candidates.filter Nat.Prime |> Finset.max
  max_prime.getD 0

/--
A385959: The auxiliary sequence $b(n)$.
$b(0) = 1$.
$b(n) = b(n-1) \cdot \frac{a(n)+1}{a(n)-1}$.
-/
noncomputable def b : ℕ → ℕ
| 0 => 1
| n + 1 =>
  let b_prev := b n;
  let p := largest_prime_divisor_property b_prev;
  -- b(n+1) = b_prev + b_prev * 2 / (p - 1)
  b_prev + b_prev * 2 / (p - 1)

/--
A385958: $a(n)$ is the largest prime $p$ such that $b(n) = b(n-1) \cdot \frac{p+1}{p-1}$ is an integer (A385959), where $b(0) = 1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n > 0 then
    largest_prime_divisor_property (b (n - 1))
  else 0

/--
Conjecture: Does this sequence contain all odd primes?
Formalization: For every odd prime $p$, there exists $n \in \mathbb{N}^+$ such that $a(n) = p$.
-/
theorem oeis_385958_conjecture_0 : ∀ (p : ℕ), Nat.Prime p → p ≠ 2 → ∃ (n : ℕ+), a n = p := by
  sorry
