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
# Half-Fibonacci sequence

$a(0) = 1, a(1) = 3$; for $n \ge 2$, $a(n) = f(a(n-1)) + f(a(n-2))$ where $f(x) = x/2$ if $x$
is even
and $f(x) = x$ if $x$ is odd.

*References:*
- [A120424](https://oeis.org/A120424)-/

namespace OeisA120424

/-- Halve even numbers, leave odd numbers unchanged. -/
def f (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else x

/-- Half-Fibonacci sequence starting with $1, 3$. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => f (a (n + 1)) + f (a n)

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 7 := by rfl

/--
Conjecture (1): The natural density of even terms in the sequence is $1/2$.-/
@[category research open, AMS 11]
theorem conjecture1 :
    Filter.Tendsto (fun n : ℕ => ((Finset.filter (fun k => a k % 2 = 0) (Finset.range n)).card
        : ℝ) / (n : ℝ))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  sorry

/--
Conjecture (2): There are infinitely many consecutive pairs that differ by 1.-/
@[category research open, AMS 11]
theorem conjecture2 :
    Set.Infinite {n : ℕ | a (n + 1) = a n + 1 ∨ a n = a (n + 1) + 1} := by
  sorry

end OeisA120424
