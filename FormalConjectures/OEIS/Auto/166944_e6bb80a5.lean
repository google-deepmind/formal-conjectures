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

/--
A166944: $a(1)=2$; $a(n) = a(n-1) + \gcd(n, a(n-1))$ if $n$ is even, $a(n) = a(n-1) + \gcd(n-2, a(n-1))$ if $n$ is odd.
-/
def a : ℕ → ℕ
| 0 => 0
| 1 => 2
| n + 1 => -- Defines a(n+1) in terms of a(n) for n >= 1. Current index is n+1 >= 2.
  let current_idx := n + 1
  let prev_a := a n
  if current_idx % 2 = 0 then
    prev_a + Nat.gcd current_idx prev_a
  else
    -- Since current_idx is odd and >= 3, current_idx - 2 is safely in ℕ.
    prev_a + Nat.gcd (current_idx - 2) prev_a


theorem a_one : a 1 = 2 := rfl

theorem a_two : a 2 = 4 := by sorry

theorem a_three : a 3 = 5 := by sorry

theorem a_four : a 4 = 6 := by sorry


-- Start of the conjecture formalization

/-- The difference sequence $d_n = a(n) - a(n-1)$. D is defined for n >= 2. -/
def d (n : ℕ) : ℕ := a n - a (n-1)

/-- A natural number `p` is the greater of a twin prime pair if `p` is prime and `p - 2` is prime. -/
def is_greater_twin_prime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p - 2)

/-- A value `R : ℕ` is a record for the sequence of differences `d(n)` if
there exists an index `n` such that $d(n)=R$, and $R$ is strictly larger
than all previous differences.
The sequence of differences starts at n=2.
-/
def is_difference_record (R : ℕ) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ d n = R ∧ (∀ k : ℕ, 2 ≤ k ∧ k < n → d k < R)

/--
Conjecture: Every record of differences $a(n)-a(n-1)$ more than 5 is the greater of twin primes (A006512).
-/
theorem oeis_166944_conjecture_0 :
  ∀ R : ℕ, 5 < R → is_difference_record R → is_greater_twin_prime R :=
by sorry
