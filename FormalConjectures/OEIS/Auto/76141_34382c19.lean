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

open List Nat

/-- Counts the number of times `pattern` appears as a contiguous sublist in `target`. -/
def list_count_infix {α : Type*} [DecidableEq α] (pattern : List α) (target : List α) : ℕ :=
  if pattern.isEmpty then 0
  else
    let n := pattern.length
    let m := target.length
    if n > m then 0
    else
      (List.range (m - n + 1)).countP fun i =>
        (target.drop i).take n = pattern

/--
The binary representation of a natural number $n$, most significant bit first, as a list of $0/1$ natural numbers.
For $n=0$, this is defined as the list $[0]$.
For $n>0$, it is the standard binary expansion without leading zeros.
We use `Nat.cast` to map the digits (which are $\mathbb{N}$) to themself.
-/
def binary_pattern_nat (n : ℕ) : List ℕ :=
  match n with
  | 0 => [0]
  | m + 1 => (Nat.digits 2 (m + 1)).reverse

/--
A076141: Number of times $n$ occurs as a binary sub-pattern of $n^2$.
Specifically, $a(n)$ is the number of times the binary pattern of $n$ is an infix of the binary pattern of $n^2$.
Let $B(k)$ be the list of $0/1$ digits of $k$ in base 2, MSB first. $a(n)$ is the number of times $B(n)$
occurs as a contiguous sublist in $B(n^2)$.
-/
def a (n : ℕ) : ℕ :=
  let pattern := binary_pattern_nat n
  let target := binary_pattern_nat (n^2)
  list_count_infix pattern target

/--
OEIS A076141 Conjecture: The number of times $n$ occurs as a binary sub-pattern of $n^2$ is at most 1 for all $n$.
A claim to Formalize: is a(n)<=1 for all n?
-/
theorem oeis_a076141_conjecture : ∀ n : ℕ, a n ≤ 1 := by sorry
