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

/-- The characteristic function of primes $\chi_P(k)$. -/
def chi_P (k : ℕ) : ℕ := if k.Prime then 1 else 0

/-- The dot product of two lists of equal length. -/
def list_dot_product (xs ys : List ℕ) : ℕ :=
  (xs.zipWith (fun a b => a * b) ys).sum

/-- The characteristic vector of primes up to `n`: $(\chi_P(1), \ldots, \chi_P(n))$ encoded as a list. -/
def b_vec (n : ℕ) : List ℕ := List.ofFn (fun i : Fin n => chi_P (i.val + 1))

/-- The cyclic autocorrelation of the first `n` terms of the characteristic function of primes,
with `j` right rotations. Right rotation by `j` is determined by left rotation by $\mathtt{n - j}$. -/
def cyclic_autocorrelation (n j : ℕ) : ℕ :=
  let b_n := b_vec n
  list_dot_product b_n (b_n.rotate (n - j))

/--
A338238: Minimum number of rotations for a second maximum partially ordered match of the first $n$ terms of the characteristic function of primes.
The sequence is defined for length $n \ge 2$. The returned value is the minimum $j \in \{1, \ldots, n-1\}$ that maximizes $C_n(j)$.
-/
noncomputable def A338238 (n : ℕ) : ℕ :=
  if h_n : n ≥ 2 then
    -- The set of rotations J = {1, 2, ..., n-1}.
    let rotations : List ℕ := (List.range n).tail

    -- M is the maximum value of C(n, j) for j ∈ J (the "second maximum").
    let M : ℕ := (rotations.map (cyclic_autocorrelation n)).maximum.getD 0

    -- Find the minimum j in rotations such that C(n, j) = M.
    -- List.find? and Option.getD are used for robust extraction from the Option type.
    rotations.find? (fun j => cyclic_autocorrelation n j = M) |>.getD 0
  else
    -- For n=0, 1, we return 1. The sequence is correctly indexed from n=2 upwards.
    1

/-- The primorial $(\cdot)\#$ of $n$, the product of primes $\le n$. -/
noncomputable def Nat_primorial (n : ℕ) : ℕ := (Finset.filter (fun p => p.Prime) (Finset.range (n + 1))).prod id

/--
Conjecture A338238: It seems that most frequent terms among the first ones assume values 1, 2, 6, 30, 210, 2310, . . . Primorials? Several scatter plots of sequences of different lengths suggest this pattern (See Link).

Formalized as: The image of the sequence $A338238$ for $n \ge 2$ contains infinitely many primorials.
-/
theorem A338238_infinitely_often_primorial_conjecture :
  Set.Infinite { val : ℕ | (∃ (n : ℕ), n ≥ 2 ∧ val = A338238 n) ∧ (∃ (m : ℕ), val = Nat_primorial m) } :=
  by sorry
