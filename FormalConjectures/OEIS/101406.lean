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

/-!
# A101406: Least $k \in \mathbb{N}$ such that $k^n(k^n-1)-1$ is a prime number.

$a(n)$ is the least $k \in \mathbb{N}$ such that $k^n(k^n-1)-1$ is a prime number.

*Reference:* [A101406](https://oeis.org/A101406)
-/

namespace OeisA101406

open Nat
open scoped Nat.Prime

/--
$a(n)$ is the least $k \in \mathbb{N}$ such that $k^n(k^n-1)-1$ is a prime number.
The sequence is indexed starting at $n=1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define the predicate P(k) using the scoped Nat.Prime
  let P (k : ℕ) : Prop := (k ^ n * (k ^ n - 1) - 1).Prime

  -- The least element of the set of natural numbers satisfying P(k).
  -- We require k > 1 since $k=1$ results in $1 \cdot (1-1) - 1 = -1$, which is not prime.
  sInf { k : ℕ | k > 1 ∧ P k }

macro "eval_a" : tactic =>
  `(tactic| (
    delta a
    apply IsLeast.csInf_eq
    constructor
    · exact by norm_num
    · intro b hb
      by_contra h
      push_neg at h
      interval_cases b <;> revert hb <;> norm_num
  ))

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_1 : a 1 = 3 := by eval_a

@[category test, AMS 11]
lemma test_a_2 : a 2 = 2 := by eval_a

@[category test, AMS 11]
lemma test_a_3 : a 3 = 3 := by eval_a

@[category test, AMS 11]
lemma test_a_4 : a 4 = 2 := by eval_a

@[category test, AMS 11]
lemma test_a_5 : a 5 = 2 := by eval_a

/--
Under the Bunyakovsky conjecture, a(n) exists for every n.

This formalizes the claim that for every $n \in \mathbb{N}^+$, the set of $k > 1$ for which
$k^n(k^n-1)-1$ is prime is non-empty. This non-emptiness ensures that $a(n)$
is a well-defined least element of a non-empty set of natural numbers.
-/
@[category research open, AMS 11]
theorem main_conjecture :
    ∀ n : ℕ, n > 0 → ∃ k : ℕ, k > 1 ∧ (k ^ n * (k ^ n - 1) - 1).Prime := by
  sorry

end OeisA101406
