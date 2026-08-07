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

open Finset Nat

/--
A230718: Smallest $n$-th power equal to a sum of some consecutive, immediately preceding, positive $n$-th powers, or 0 if none.
$a(n)$ is the smallest solution to $k^n + (k+1)^n + \dots + (k+m)^n = (k+m+1)^n$ with $k > 0$ and $m > 0$, or $0$ if none.
-/
noncomputable def A230718 (n : ℕ) : ℕ :=
  if n = 0 then 1 else
  -- Let $N = k+m+1$
  let P (N : ℕ) : Prop :=
    N ≥ 3 ∧ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧
    (Finset.Ico k N).sum (fun i => i ^ n) = N ^ n

  let Solutions : Set ℕ := { N : ℕ | P N }

  let N_min := sInf Solutions

  -- If Solutions is empty, N_min = 0 (since ℕ is OrderBot), so we return 0.
  -- Otherwise, N_min ≥ 3, and we return N_min ^ n.
  if N_min = 0 then 0 else N_min ^ n


theorem a_zero : A230718 0 = 1 := by
  trivial

theorem a_one : A230718 1 = 3 := by
  rw [A230718]
  exact (.trans (congr_arg (fun p=>ite (p=0) 0 (p^1)) ( IsLeast.csInf_eq ⟨ (by repeat constructor), fun and=>And.left⟩)) rfl )

theorem a_two : A230718 2 = 25 := by
  (inhabit Int)
  delta A230718
  push_cast+decide[←and_assoc,← Finset.mem_Icc,IsLeast.csInf_eq (Nat.isLeast_find ⟨5, _⟩)]

theorem a_three : A230718 3 = 216 := by
  norm_num [A230718]
  push_cast+decide[←and_assoc,← Finset.mem_Icc,IsLeast.csInf_eq (Nat.isLeast_find ⟨6,_⟩)]

/-- oeis_230718_conjecture_1: Is a(n) $\ne 0$ for any $n > 3$?
The conjecture is that $a(n) = 0$ for all $n > 3$.
The Erdos-Moser equation is the case $k = 1$. They conjecture that the only solution is $m = n = 1$.
Any counterexample would be a case of $a(n) > 0$ with $n > 3$.
And such a case with $k = 1$ would be a counterexample to the Erdos-Moser conjecture. -/
theorem oeis_230718_conjecture_1 : ∀ (n : ℕ), n > 3 → A230718 n = 0 := by
  sorry
