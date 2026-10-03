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
# Least primitive prime divisor of the Franel numbers of order $4$

Let $f_r(n) = \sum_{k=0}^n \binom{n}{k}^r$ be the Franel number of order $r$. The sequence
$a(n)$ is the least prime divisor of $f_4(n)$ (A005260) that does not divide any previous
term $f_4(k)$ with $1 \le k < n$, or $1$ if no such prime divisor exists.

*References:*
- [A242174](https://oeis.org/A242174)
-/

namespace OeisA242174

open Finset

/-- The Franel number of order $r$: $f_r(n) = \sum_{k=0}^n \binom{n}{k}^r$. -/
def franel (r n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), n.choose k ^ r

/-- Least prime divisor of $f_r(n)$ that does not divide $f_r(k)$ for any $1 \le k < n$,
or $1$ if no such prime divisor exists. -/
def primitivePrimeDivisorFranel (r n : ℕ) : ℕ :=
  let b := franel r
  ((b n).primeFactorsList.filter fun p =>
    (List.range' 1 (n - 1)).all fun k => !(p ∣ b k)).head?.getD 1

/-- Least prime divisor of $A005260(n) = \sum_{k=0}^n \binom{n}{k}^4$ that does not divide any
previous term $A005260(k)$ ($1 \le k < n$), or $1$ if no such prime divisor exists. -/
def a (n : ℕ) : ℕ :=
  primitivePrimeDivisorFranel 4 n

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  native_decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  native_decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 41 := by
  native_decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  native_decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 7 := by
  native_decide

/--
Conjecture: $a(n)$ is prime for any $n > 0$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 0 < n) : (a n).Prime := by
  sorry

/--
"In general, for any $r > 2$, if $n$ is large enough then $f_r(n) = \sum_{k=0}^n \binom{n}{k}^r$
has a prime divisor which does not divide any previous terms $f_r(k)$ with $k < n$."
-/
@[category research open, AMS 11]
theorem conjecture2 (r : ℕ) (hr : 2 < r) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → primitivePrimeDivisorFranel r n ≠ 1 := by
  sorry

end OeisA242174
