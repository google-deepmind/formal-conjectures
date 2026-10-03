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
# Floor of $n^2$ divided by the sum of products of consecutive divisors of $n$

Let $n \ge 2$ be a positive integer with divisors $1 = d_1 < d_2 < \dots < d_k = n$, and let
$s = d_1 d_2 + d_2 d_3 + \dots + d_{k-1} d_k$. The sequence $a(n)$ lists the values
$\lfloor n^2 / s \rfloor$.

*References:*
- [A251758](https://oeis.org/A251758)
-/

namespace OeisA251758

open Nat List

/-- The primary sequence $a(n) = \lfloor n^2 / s \rfloor$, where $s$ is the sum of products of
consecutive divisors of $n$ in increasing order. -/
def a (n : ℕ) : ℕ :=
  let divisorsList : List ℕ := (List.range (n + 1)).filter (· ∣ n)
  let sList : List ℕ :=
    (divisorsList.zip divisorsList.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := sList.sum
  if s = 0 then 0 else n ^ 2 / s

/-- Number of primes strictly less than $n$. -/
def numPrimesLt (n : ℕ) : ℕ :=
  ((Finset.range n).filter Nat.Prime).card

/-- Product of the first $k$ primes. -/
noncomputable def primorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

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
"Conjecture: Terms $x$, where $a(x)=n$, $x=p\#k/p\#j$, $p\#i$ is the $i$-th primorial, $k>j$ is
suitable large $k$ and $j$ is the number of primes less than $n$. As an example, $n=9$,
$x = p\#7/p\#4 = 2431$. For $n=10$, $x = p\#6/p\#4 = 143$ although $121 = 11^2$ is the least $x$
where $a(x)=10$ (see formula section). For $n=8$, $x = p\#12/p\#4, p\#13/p\#4, p\#14/p\#4,
p\#15/p\#4, p\#16/p\#4$, etc. But is $p\#12/p\#4$ the least such $x$?"
-/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) ↔
      IsLeast {x : ℕ | ∃ k > numPrimesLt 8,
        x = primorial k / primorial (numPrimesLt 8) ∧ a x = 8}
        (primorial 12 / primorial (numPrimesLt 8)) := by
  sorry

end OeisA251758
