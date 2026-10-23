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
# Lengths of the 2-dense sublists of divisors of $n$

Write the divisors of $n$ in increasing order and split this list between consecutive divisors
$d < d'$ with $d' > 2d$. The pieces are the 2-dense sublists of divisors of $n$. Row $n$ of the
triangle lists their lengths. Row $n$ of A384225 lists the numbers of odd terms in them.

*References:*
- [A384222](https://oeis.org/A384222)
- [A384225](https://oeis.org/A384225)
-/

@[expose] public section

namespace OeisA384222

/-- The divisors of $n$ in increasing order. -/
def divisorList (n : ℕ) : List ℕ := (List.range' 1 n).filter (· ∣ n)

/-- The 2-dense sublists of divisors of $n$. -/
def denseSublists (n : ℕ) : List (List ℕ) :=
  (divisorList n).splitBy fun d d' => d' ≤ 2 * d

/-- Row $n$ of the triangle: the lengths of the 2-dense sublists of divisors of $n$. -/
def row (n : ℕ) : List ℕ := (denseSublists n).map List.length

/-- Row $n$ of A384225: the numbers of odd terms in the 2-dense sublists of divisors of $n$. -/
def oddRow (n : ℕ) : List ℕ := (denseSublists n).map (List.countP fun d => d % 2 = 1)

@[category test, AMS 11]
theorem row_1 : row 1 = [1] := by decide

@[category test, AMS 11]
theorem row_3 : row 3 = [1, 1] := by decide

@[category test, AMS 11]
theorem row_6 : row 6 = [4] := by decide

@[category test, AMS 11]
theorem row_9 : row 9 = [1, 1, 1] := by decide

@[category test, AMS 11]
theorem row_10 : row 10 = [2, 2] := by decide

@[category test, AMS 11]
theorem row_70 : row 70 = [2, 4, 2] := by decide

@[category test, AMS 11]
theorem oddRow_70 : oddRow 70 = [1, 2, 1] := by decide

/--
"Conjecture 1: row n is a palindromic composition of A000005(n)."

A composition of $A000005(n)$ is a list of positive integers with sum $A000005(n)$, the number
of divisors of $n$.

Solved by Claude (Anthropic) prompted by otoinobuo. The map $d \mapsto n/d$ reverses the list
of divisors and preserves the ratio of consecutive divisors.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/otoi-lab/oeis-lean-proofs/blob/14f275b8b370bcf76213de10bb3f8fda84a6461e/OeisProofs/FC/A384222.lean#L26-L31"]
theorem conjecture_1 (n : ℕ) (hn : 0 < n) :
    (∀ k ∈ row n, 0 < k) ∧ (row n).sum = n.divisors.card ∧ (row n).reverse = row n := by
  sorry

/--
"T(n,k) = A384225(n,k) * A001511(n) = A384225(n,k) * A000005(n) / A001227(n). (conjectured)."
- Omar E. Pol, Apr 13 2026

This formalizes the first equality. The ruler function is $A001511(n) = \nu_2(n) + 1$.

Solved by Claude (Anthropic) prompted by otoinobuo. If $d$ and $2d$ divide $n$, then they lie
in the same 2-dense sublist. So each sublist is a union of sets $\{o, 2o, \dots, 2^{\nu_2(n)} o\}$
with $o$ odd.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/otoi-lab/oeis-lean-proofs/blob/14f275b8b370bcf76213de10bb3f8fda84a6461e/OeisProofs/FC/A384222.lean#L33-L36"]
theorem conjecture_formula (n : ℕ) (hn : 0 < n) :
    row n = (oddRow n).map ((padicValNat 2 n + 1) * ·) := by
  sorry

end OeisA384222
