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

open Nat Function Set
open scoped Classical

/-- The step function for the Collatz sequence: $n/2$ if $n$ is even, $3n+1$ if $n$ is odd. -/
def collatz_step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2
  else 3 * n + 1

/--
A006577: The number of iterations required to turn $n$ into 1 in the Collatz Conjecture.
Defined as $\min \{k \in \mathbb{N} \mid \text{collatz\_step}^k(n) = 1\}$.
This noncomputable definition uses the set infimum $\text{sInf}$, assuming the Collatz conjecture holds for $n>0$.
-/
noncomputable def A006577_steps (n : ℕ) : ℕ :=
  if n = 0 then 0
  else sInf {k : ℕ | (collatz_step^[k]) n = 1}

/--
A153330: Differences in adjacent elements of the sequence quantifying the steps needed for $n$ to converge to 1 in the Collatz Conjecture.
$$a(n) = \text{A006577}(n+1) - \text{A006577}(n) \text{ for } n>0.$$
-/
noncomputable def A153330 (n : ℕ) : ℤ :=
  if n = 0 then 0 -- The sequence is defined for $n \ge 1$.
  else (A006577_steps (n + 1) : ℤ) - (A006577_steps n : ℤ)

-- Test theorems provided in prompt (not required for submission, but kept for completeness of context)
theorem a_one : A153330 1 = 1 := by sorry
theorem a_two : A153330 2 = 6 := by sorry
theorem a_three : A153330 3 = -5 := by sorry
theorem a_four : A153330 4 = 3 := by sorry

/-- The set of indices $n \ge 1$ for which $\text{A153330}(n)$ equals a given value $v$. -/
def A153330_indices (v : ℤ) : Set ℕ :=
  {n : ℕ | n > 0 ∧ A153330 n = v}

/--
Conjecture 2: 1, 6 and 16 appear only once and 3 appears twice in the sequence,
i.e., a(1) = 1, a(2) = 6, a(4) = a(5) = 3, and a(8) = 16.
-/
theorem oeis_a153330_conjecture_2 :
    A153330_indices 1 = {1} ∧
    A153330_indices 6 = {2} ∧
    A153330_indices 16 = {8} ∧
    A153330_indices 3 = {4, 5} :=
by sorry
