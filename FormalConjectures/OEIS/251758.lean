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
# Floor of $n^2$ divided by the sum of products of consecutive divisors of $n$

Let $n \ge 2$ be a positive integer with divisors $1 = d_1 < d_2 < \dots < d_k = n$, and let
$s = d_1 d_2 + d_2 d_3 + \dots + d_{k-1} d_k$. The sequence $a(n)$ lists the values
$\lfloor n^2 / s \rfloor$.

*References:*
- [A251758](https://oeis.org/A251758)
-/

@[expose] public section

namespace OeisA251758

open Nat List

/-- $\lfloor n^2 / s \rfloor$, where $s$ is the sum of products of consecutive divisors of $n$ in
increasing order. -/
def a (n : ℕ) : ℕ :=
  let divisorsList : List ℕ := (List.range (n + 1)).filter (· ∣ n)
  let sList : List ℕ :=
    (divisorsList.zip divisorsList.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := sList.sum
  if s = 0 then 0 else n ^ 2 / s

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 5 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 1 := by decide

/--
Let $p\#_i$ denote the $i$-th primorial (`Nat.kthPrimorial i`). For $n = 8$, the primorial ratios
$x = p\#_{12}/p\#_4, p\#_{13}/p\#_4, p\#_{14}/p\#_4, p\#_{15}/p\#_4, p\#_{16}/p\#_4, \dots$
satisfy $a(x) = 8$. Is $p\#_{12}/p\#_4 = 35336848261$ the least $x \ge 2$ such that $a(x) = 8$?

"For $n=8$, $x = p\#12/p\#4, p\#13/p\#4, p\#14/p\#4, p\#15/p\#4, p\#16/p\#4$, etc.
But is $p\#12/p\#4$ the least such $x$?"
- _Robert G. Wilson v_, Dec 18 2014
-/
@[category research open, question, AMS 11]
theorem conjecture :
    IsLeast {x : ℕ | 2 ≤ x ∧ a x = 8}
      (Nat.kthPrimorial 12 / Nat.kthPrimorial (Nat.primeCounting' 8)) := by
  sorry

end OeisA251758
