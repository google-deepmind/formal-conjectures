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
# Number of positive integers $\le n$ strongly prime to $n$

The number of positive integers $\le n$ that are strongly prime to $n$. An integer $k$ is
strongly prime to $n$ if and only if $k$ is relatively prime to $n$ and $k$ does not divide
$n - 1$. For $n > 1$, $a(n) = \phi(n) - \tau(n-1)$.

*References:*
- [A181830](https://oeis.org/A181830)
- M. Scroggs, "Braiding, pt. 2. Two results and a conjecture",
  http://www.mscroggs.co.uk/blog/31-/

namespace OeisA181830

/-- Number of positive integers $\le n$ that are strongly prime to $n$. -/
def a (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else Nat.totient n - (Nat.divisors (n - 1)).card

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by rfl

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

/-- Value of the sequence `a` at 7. -/
@[category test, AMS 11]
theorem a_7 : a 7 = 2 := by decide

/-- The number of cardboard braids that work with $n$ slots. -/
axiom cardboardBraidsCount : ℕ → ℕ

/--
"It is conjectured (see Scroggs link) that a(n) is also the number of cardboard braids that
work with n slots." - Matthew Scroggs, Sep 23 2017-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) : a n = cardboardBraidsCount n := by
  sorry

end OeisA181830
