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
# Primes of the form $F_n+L_{n+1}$

The third diagonal of the determinant Hosoya triangle contains the numbers $F_n+L_{n+1}$,
where $F_n$ and $L_n$ are the Fibonacci and Lucas numbers. Since
$L_{n+1}=F_n+F_{n+2}$, these numbers are $2F_n+F_{n+2}$. Their prime values begin
$5,23,37,97,157,1741,\ldots$. These are the terms of OEIS A091157 after its initial $3$,
which comes from extending the Fibonacci and Lucas indices to $n=-1$.

*References:*
- H.-Y. Ching, R. Flórez, F. Luca, A. Mukherjee, and J. C. Saunders,
  [Primes and composites in the determinant Hosoya triangle](https://arxiv.org/abs/2211.10788),
  introduction and Question 1 of Section 5.
- [OEIS A091157](https://oeis.org/A091157)
-/

@[expose] public section

namespace Arxiv.«2211.10788»

/-- The sum $F_n+L_{n+1}=2F_n+F_{n+2}$, using $F_0=0$ and $F_1=1$. -/
def lucasFibonacciSum (n : ℕ) : ℕ := 2 * Nat.fib n + Nat.fib (n + 2)

@[category test, AMS 11]
theorem lucas_fibonacci_sum_zero : lucasFibonacciSum 0 = 1 := by decide

@[category test, AMS 11]
theorem lucas_fibonacci_sum_one : lucasFibonacciSum 1 = 4 := by decide

@[category test, AMS 11]
theorem lucas_fibonacci_sum_two : lucasFibonacciSum 2 = 5 := by decide

@[category test, AMS 11]
theorem lucas_fibonacci_sum_three : lucasFibonacciSum 3 = 9 := by decide

@[category test, AMS 11]
theorem lucas_fibonacci_sum_four : lucasFibonacciSum 4 = 14 := by decide

@[category test, AMS 11]
theorem prime_values :
    lucasFibonacciSum 2 = 5 ∧ lucasFibonacciSum 5 = 23 ∧ lucasFibonacciSum 6 = 37 ∧
      lucasFibonacciSum 8 = 97 ∧ lucasFibonacciSum 9 = 157 ∧
      (lucasFibonacciSum 2).Prime ∧ (lucasFibonacciSum 5).Prime ∧
      (lucasFibonacciSum 6).Prime ∧
      (lucasFibonacciSum 8).Prime ∧ (lucasFibonacciSum 9).Prime := by
  norm_num [lucasFibonacciSum]

@[category test, AMS 11]
theorem early_nonprimes :
    ¬ (lucasFibonacciSum 0).Prime ∧ ¬ (lucasFibonacciSum 1).Prime ∧
      ¬ (lucasFibonacciSum 3).Prime ∧ ¬ (lucasFibonacciSum 4).Prime := by
  decide

/-- The neighboring sums satisfy the Fibonacci recurrence. -/
@[category API, AMS 11]
theorem lucas_fibonacci_sum_recurrence (n : ℕ) :
    lucasFibonacciSum (n + 2) = lucasFibonacciSum (n + 1) + lucasFibonacciSum n := by
  have h0 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  have h2 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
    simpa [Nat.add_assoc] using (Nat.fib_add_two (n := n + 2))
  change 2 * Nat.fib (n + 2) + Nat.fib (n + 4) =
    (2 * Nat.fib (n + 1) + Nat.fib (n + 3)) + (2 * Nat.fib n + Nat.fib (n + 2))
  omega

/--
"Are there infinitely many primes of this form?"
The form in the introduction is $F_n+L_{n+1}$.
-/
@[category research open, question, AMS 11]
theorem infinitely_many_lucas_fibonacci_sum_primes :
    {p : ℕ | p.Prime ∧ ∃ n, p = lucasFibonacciSum n}.Infinite := by
  sorry

end Arxiv.«2211.10788»
