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

open Nat List Finset

/--
A251758: Let $n \ge 2$ be a positive integer with divisors $1 = d_1 < d_2 < \dots < d_k = n$,
and $s = d_1 d_2 + d_2 d_3 + \dots + d_{k-1} d_k$.
The sequence lists the values $a(n) = \lfloor n^2 / s \rfloor$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Get the list of divisors in increasing order.
  let divisors_list : List ℕ := (Nat.divisors n).sort (· ≤ ·)

  -- Calculate s = sum of product of successive divisors: s = d₁d₂ + d₂d₃ + ...
  let s_list : List ℕ := (divisors_list.zip divisors_list.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := s_list.sum

  -- The result is ⌊n^2 / s⌋. Since Nat.div is floor division, and s > 0 for n >= 2.
  if s = 0 then 0
  else n ^ 2 / s


theorem a_two : a 2 = 2 := by
  simp_all[a]
  norm_num[Nat.Prime.divisors,Finset.sort_insert]

theorem a_three : a 3 = 3 := by
  simp_rw [a]
  norm_num [ Finset.sort_insert,Nat.Prime.divisors]

theorem a_four : a 4 = 1 := by
  delta a
  norm_num+decide only[ Finset.sort_insert, true, Finset.sort_singleton]
  simp_all+decide -contextual [show(4).divisors = {1,2,4}by constructor, Finset.sort_insert]

theorem a_five : a 5 = 5 := by
  delta a
  norm_num [ Finset.sort_insert, true,Nat.Prime.divisors]

/-- The set of integers $n \ge 2$ such that $a(n)=k$. -/
def first_occurrence_set (k : ℕ) : Set ℕ :=
  { n : ℕ | n ≥ 2 ∧ a n = k }

/--
A251758 Conjecture: Terms $x$, where $a(x)=n$, $x=p_{\#k}/p_{\#j}$, $p_{\#i}$ is the $i$-th primorial, $k>j$ is suitable large $k$ and $j$ is the number of primes less than $n$.
First occurrence of $n \ge 1$: 4, 2, 3, 25, 5, 49, 7, ??? $\le 35336848261$, 2431, 121, 11, 169, 13, 6678671, 7429, 289, 17, 361, 19, 31367009, 20677, 529, 23, ... .
Formalizing the claim that the listed numbers are the smallest $n$ such that $a(n)=k$.
-/
theorem a251758_conjecture_first_occurrences :
  (IsLeast (first_occurrence_set 1) 4) ∧
  (IsLeast (first_occurrence_set 2) 2) ∧
  (IsLeast (first_occurrence_set 3) 3) ∧
  (IsLeast (first_occurrence_set 4) 25) ∧
  (IsLeast (first_occurrence_set 5) 5) ∧
  (IsLeast (first_occurrence_set 6) 49) ∧
  (IsLeast (first_occurrence_set 7) 7) ∧
  (IsLeast (first_occurrence_set 9) 2431) ∧
  (IsLeast (first_occurrence_set 10) 121) ∧
  (IsLeast (first_occurrence_set 11) 11) ∧
  (IsLeast (first_occurrence_set 12) 169) ∧
  (IsLeast (first_occurrence_set 13) 13) ∧
  (IsLeast (first_occurrence_set 14) 6678671) ∧
  (IsLeast (first_occurrence_set 15) 7429) ∧
  (IsLeast (first_occurrence_set 16) 289) ∧
  (IsLeast (first_occurrence_set 17) 17)
  := by sorry
