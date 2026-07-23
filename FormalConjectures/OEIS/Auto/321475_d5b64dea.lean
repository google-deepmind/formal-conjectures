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

open Nat List

/--
A321475: Zeroless factorials (version 2): $a(0) = 1$, and for any $n > 0$,
$a(n) = \operatorname{noz}(1 \cdot \operatorname{noz}(2 \cdot \ldots \cdot \operatorname{noz}((n-1) \cdot n)))$,
where $\operatorname{noz}(n) = A004719(n)$ omits the zeros from $n$.
-/
noncomputable def A321475 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    -- Helper function noz(k) to omit zeros from k (A004719)
    let noz (k : ℕ) : ℕ :=
      ofDigits 10 (filter (fun d : ℕ => d ≠ 0) (digits 10 k))

    -- The calculation is a tail-recursive loop modeling the nested operations.
    -- i is the descending multiplier, P is the accumulated product/result.
    let rec loop (i : ℕ) (P : ℕ) : ℕ :=
      if i = 0 then P
      -- Apply the next step: noz(i * P) and continue with the next multiplier i-1.
      else loop (i - 1) (noz (i * P))

    -- Initial call: multiplier starts at n - 1, initial value is n.
    loop (n - 1) n


theorem a_zero : A321475 0 = 1 := by
  sorry

theorem a_one : A321475 1 = 1 := by
  sorry

theorem a_two : A321475 2 = 2 := by
  sorry

theorem a_three : A321475 3 = 6 := by
  sorry


/--
%C A321475 Is this sequence bounded?
-/
theorem oeis_321475_conjecture_0 : ∃ M : ℕ, ∀ n : ℕ, A321475 n ≤ M := by sorry
