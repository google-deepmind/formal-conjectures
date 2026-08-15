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

open Nat Finset BigOperators

/--
A297707: $a(n) = \prod_{k=1}^{n-1} n!k$, where $n!k$ is $k$-tuple factorial of $n$.
The $k$-tuple factorial of $n$ is defined as
$$n!_k = \prod_{j=0}^{\lfloor(n-1)/k\rfloor} (n - j k)$$
-/
def A297707 (n : ℕ) : ℕ :=
  let k_tuple_factorial (n k : ℕ) : ℕ :=
    if 0 < k then
      -- The number of terms is determined by the upper bound $\lfloor (n-1)/k \rfloor$.
      let max_j : ℕ := (n - 1) / k
      Finset.prod (range (max_j + 1)) fun j => n - j * k
    else
      1 -- Case k=0 is not used in the sequence, but we must be total.

  -- The overall sequence is $\prod_{k=1}^{n-1} n!_k$, given by Ico 1 n.
  Finset.prod (Ico 1 n) fun k => k_tuple_factorial n k


theorem a_one : A297707 1 = 1 := by
  constructor

theorem a_two : A297707 2 = 2 := by
  rfl

theorem a_three : A297707 3 = 18 := by
  delta A297707
  rfl

theorem a_four : A297707 4 = 768 := by
  constructor

/-- A natural number greater than 1 that is not prime. -/
def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬ Nat.Prime n

/-- The largest prime number strictly less than `n`.
    Returns 0 if no such prime exists (i.e., n ≤ 2). -/
noncomputable def Nat.prevPrime (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range n)).max.getD 0

local notation "a" => A297707

/-- oeis_297707_conjecture_0: What is the least n > 2 for which a(n) - prevprime(a(n)) is a composite number?
If such a number n exists, it is greater than 250. -/
theorem oeis_297707_conjecture_0 :
  ∀ n, 2 < n → IsComposite (a n - Nat.prevPrime (a n)) → 250 < n :=
by sorry
