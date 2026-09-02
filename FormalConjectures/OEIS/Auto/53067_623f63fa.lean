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

open Nat List

/-- The $n$-th triangular number, $T_n = \frac{n(n+1)}{2}$. -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Concatenates two natural numbers $a$ and $b$ base 10. -/
def concatenate_nats (a b : ℕ) : ℕ :=
  a * (10 ^ (Nat.digits 10 b).length) + b

/--
A053067: $a(n)$ is the concatenation of next $n$ numbers (omit leading 0's).
Specifically, $a(n)$ is the concatenation of the integers from $\frac{(n-1)n}{2} + 1$ up to $\frac{n(n+1)}{2}$.
-/
def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    -- The starting number is $T_{n-1} + 1$. We use n - 1 which is safe since n ≠ 0.
    let start_num : ℕ := triangular (n - 1) + 1
    -- The ending number is $T_n$.
    let end_num : ℕ := triangular n

    -- List.Ico start (end + 1) gives [start, start + 1, ..., end]
    let numbers_to_concat : List ℕ := List.Ico start_num (end_num + 1)

    -- Concatenate the numbers from left to right. The initial accumulator 0 correctly handles the first element.
    numbers_to_concat.foldl concatenate_nats 0

theorem a_one : a 1 = 1 := by
  simp_all[a]
  norm_num+decide [concatenate_nats,triangular]

theorem a_two : a 2 = 23 := by
  inhabit Real
  apply(add_comm _ _).trans
  norm_num[concatenate_nats,triangular]

theorem a_three : a 3 = 456 := by
  delta a
  norm_num[concatenate_nats,triangular,List.Ico]
  norm_num[concatenate_nats,List.range']

theorem a_four : a 4 = 78910 := by
  delta a
  push_cast [concatenate_nats,triangular,List.Ico,List.foldl]
  norm_num[concatenate_nats,List.range']

/--
The second term is a prime. When is the next prime, if there is another? - _N. J. A. Sloane_, Dec 16 2016
Formalized as the strongest natural conjecture: $a(n)$ is prime if and only if $n=2$.
-/
theorem oeis_53067_conjecture_0 : ∀ n : ℕ, Nat.Prime (a n) ↔ n = 2 := by
  sorry
