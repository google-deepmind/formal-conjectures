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
The OEIS sequence A241922: Smallest $k^2 \ge 0$ such that $n-k^2$ is semiprime, or $a(n)=2$ if there is no such $k^2$.
A number $m$ is semiprime if $\Omega(m)=2$, where $\Omega(m)$ is the number of prime factors of $m$ counted with multiplicity.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- $\Omega(m)$ function definition.
  let omega (m : ℕ) : ℕ :=
    if m ≤ 1 then 0
    else (Nat.factorization m).sum (fun _ k => k)

  -- Semiprime predicate as a Boolean function.
  let is_semiprime (m : ℕ) : Bool := omega m == 2

  -- The maximum $k$ to check is $\lfloor \sqrt{n} \rfloor$.
  let k_max := Nat.sqrt n

  -- We search the list of candidates $\{0, 1, \dots, k_{\max}\}$ in ascending order.
  let k_candidates := List.range (k_max + 1)

  -- List.find? returns the smallest k satisfying the predicate, which minimizes k^2.
  match k_candidates.find? (fun k => is_semiprime (n - k * k)) with
  | some k => k * k
  | none   => 2

-- Auxiliary definitions for the conjecture

/--
The Goldbach binary conjecture states that every even integer greater than 2 is the sum of two prime numbers.
-/
def goldbach_binary_conjecture : Prop :=
  ∀ n : ℕ, Even n ∧ n > 2 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- A number is in A100570 if A241922(n) = 2.
A100570: Numbers $n$ such that $n-k^2$ is never semiprime for $0 \le k^2 \le n$.
-/
def is_A100570 (n : ℕ) : Prop := a n = 2

theorem a_one : a 1 = 2 := by
  trivial

theorem a_two : a 2 = 2 := by
  norm_num[a]
  norm_num[List.range_succ]

theorem a_three : a 3 = 2 := by
  delta a
  norm_num [List.range_succ]

theorem a_four : a 4 = 0 := by
  norm_num[a, false]
  norm_num+decide[List.range_succ,List.find?_cons]
  norm_num[ Finsupp.sum,Nat.primeFactors,←(4).primeFactorsList_count_eq,Nat.primeFactorsList]

/-- C A241922 All these numbers are in A100570. Thus the Goldbach binary conjecture is true if and only if A100570 does not contain perfect squares. -/
theorem oeis_241922_conjecture_1 :
  goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n :=
by sorry
