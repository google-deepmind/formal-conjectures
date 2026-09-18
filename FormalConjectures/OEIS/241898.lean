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

import FormalConjecturesUtil

/-!
# Largest smallest-base in a decomposition of $n$ into at most four squares

The sequence $a(n)$ is the largest integer $k$ such that $n = k^2 + \dots$ is a
decomposition of $n$ into a sum of at most four nondecreasing squares:
$$a(n) = \max \{k \ge 1 : \exists b_1, b_2, b_3 \in \{0\} \cup [k, n],
  k^2 + b_1^2 + b_2^2 + b_3^2 = n\}$$

*References:*
- [A241898](https://oeis.org/A241898)
-/

namespace OeisA241898

open Finset

/-- Predicate testing whether $k$ is the smallest base in a decomposition of $n$ into a sum
of at most four squares. -/
def IsValidBase (n k : ℕ) : Bool :=
  let S := 0 :: List.range' k (n - k + 1)
  0 < k && S.any fun b1 => S.any fun b2 => S.any fun b3 =>
    k ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2 == n

/-- Largest integer $k$ such that $n = k^2 + \dots$ is a decomposition of $n$ into a sum
of at most four nondecreasing squares. -/
def a (n : ℕ) : ℕ :=
  ((Icc 1 n).filter (fun k => IsValidBase n k)).max.getD 0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  decide

/--
"From the data that I have, it would seem that $a(n)$ is greater than $7$ for all $n > 599$."
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 599 < n) : 7 < a n := by
  sorry

/--
"By Lagrange's Theorem every number can be written as a sum of four squares. Can the same be
said of the set of $\{a^2 \mid a \text{ is any integer not equal to } 7\}$?"
-/
@[category research open, AMS 11]
theorem conjecture2 :
    answer(sorry) ↔ ∀ n : ℕ, ∃ a b c d : ℕ,
      a ≠ 7 ∧ b ≠ 7 ∧ c ≠ 7 ∧ d ≠ 7 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  sorry

end OeisA241898
