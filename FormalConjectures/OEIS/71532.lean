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
# Alternating sum of signs of powers of $3/2$

The sequence $a(n) = -\sum_{k=1}^n (-1)^{\lfloor (3/2)^k \rfloor}$.

*References:*
- [A071532](https://oeis.org/A071532)-/

namespace OeisA71532

open Finset Filter
open scoped Asymptotics

/-- The sequence $a(n) = -\sum_{k=1}^n (-1)^{\lfloor (3/2)^k \rfloor}$. -/
def a (n : ℕ) : ℤ :=
  - ∑ k ∈ Icc 1 n, (-1 : ℤ) ^ (3 ^ k / 2 ^ k)

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
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
theorem a_5 : a 5 = 3 := by
  decide

/--
Is $a(n) > 0$ for all $n > 2$?
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 2 < n) : 0 < a n := by
  sorry

/--
For $n$ large enough, does $a(n) > \sqrt{n}$ always hold?
-/
@[category research open, AMS 11]
theorem conjecture2 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (a n : ℝ) > Real.sqrt (n : ℝ) := by
  sorry

/--
Conjecture: asymptotically, $a(n) \sim C \log(n)^2$ for some constant $C > 0$.
-/
@[category research open, AMS 11]
theorem conjecture3 :
    ∃ C : ℝ, 0 < C ∧ (fun n : ℕ ↦ (a n : ℝ)) ~[atTop] (fun n : ℕ ↦ C * Real.log (n : ℝ) ^ 2) := by
  sorry

/--
Conjecture: the constant $C$ in $a(n) \sim C \log(n)^2$ is approximately $1.4$.
-/
@[category research open, AMS 11]
theorem conjecture3_value :
    let C : ℝ := answer(sorry)
    |C - 1.4| < 0.1 ∧
      (fun n : ℕ ↦ (a n : ℝ)) ~[atTop] (fun n : ℕ ↦ C * Real.log (n : ℝ) ^ 2) := by
  sorry

end OeisA71532

