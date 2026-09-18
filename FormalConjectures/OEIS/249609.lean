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
# Smallest $m \in [1, n]$ such that $\binom{n}{m}$ is evil

The sequence $a(n)$ is the smallest $m$ with $1 \le m \le n$ such that $\binom{n}{m}$ is an evil
number (A001969, having an even number of $1$s in its binary expansion), or $0$ if no such $m$
exists.

*References:*
- [A249609](https://oeis.org/A249609)
-/

namespace OeisA249609

open Nat List

/-- Boolean check for whether a natural number is evil (even number of set bits in base $2$). -/
def isEvil (k : ℕ) : Bool :=
  (Nat.digits 2 k).count 1 % 2 == 0

/-- The primary sequence $a(n)$: smallest $1 \le m \le n$ such that $\binom{n}{m}$ is evil,
or $0$ if no such $m$ exists. -/
def a (n : ℕ) : ℕ :=
  ((List.range' 1 n).find? fun m => isEvil (n.choose m)).getD 0

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

/-- Conjecture: there are only five $n$ ($0, 1, 2, 7, 8$) for which all entries of the $n$-th
Pascal row (A007318) are odious (A000069), which is equivalent to $a(n) = 0$. -/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) :
    a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  sorry

end OeisA249609
