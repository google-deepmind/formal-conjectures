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
# Maximum number of terms in a 2-dense sublist of divisors of $n$

Write the divisors of $n$ in increasing order and split this list between consecutive divisors
$d < d'$ with $d' > 2d$. The pieces are the 2-dense sublists of divisors of $n$. The sequence
gives the maximum number of terms in such a sublist.

*References:*
- [A400194](https://oeis.org/A400194)
- [A400195](https://oeis.org/A400195)
- [A384222](https://oeis.org/A384222)
-/

@[expose] public section

namespace OeisA400194

/-- The divisors of $n$ in increasing order. -/
def divisorList (n : ℕ) : List ℕ := (List.range' 1 n).filter (· ∣ n)

/-- The 2-dense sublists of divisors of $n$. -/
def denseSublists (n : ℕ) : List (List ℕ) :=
  (divisorList n).splitBy fun d d' => d' ≤ 2 * d

/-- The maximum number of terms in a 2-dense sublist of divisors of $n$. -/
def a (n : ℕ) : ℕ := ((denseSublists n).map List.length).foldr max 0

/-- The maximum number of odd terms in a 2-dense sublist of divisors of $n$ (A400195). -/
def b (n : ℕ) : ℕ := ((denseSublists n).map (List.countP fun d => d % 2 = 1)).foldr max 0

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 4 := by decide

@[category test, AMS 11]
theorem a_12 : a 12 = 6 := by decide

@[category test, AMS 11]
theorem a_36 : a 36 = 9 := by decide

@[category test, AMS 11]
theorem b_30 : b 30 = 4 := by decide

set_option linter.style.formal_proof_palomar false in
/--
"Conjecture: a(n) is the product of the ruler function of n and the maximum number of odd terms
in a 2-dense sublist of divisors of n."

"Conjecture: a(n) = A001511(n) * A400195(n)."

The ruler function is $A001511(n) = \nu_2(n) + 1$.

Solved by Claude (Anthropic) prompted by otoinobuo. If $d$ and $2d$ divide $n$, then they lie
in the same 2-dense sublist. So each sublist is a union of sets $\{o, 2o, \dots, 2^{\nu_2(n)} o\}$
with $o$ odd.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/otoi-lab/oeis-lean-proofs/blob/14f275b8b370bcf76213de10bb3f8fda84a6461e/OeisProofs/FC/A400194.lean#L26-L27"]
theorem conjecture (n : ℕ) (hn : 0 < n) : a n = (padicValNat 2 n + 1) * b n := by
  sorry

end OeisA400194
