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
# $a(1)=1, a(2)=1, a(n)=(2^{a(n-1)} + 1)/a(n-2)$

The sequence is defined by $a(1) = 1, a(2) = 1$, and for $n \ge 3$,
$$a(n) = \frac{2^{a(n-1)} + 1}{a(n-2)}$$

*References:*
- [A078590](https://oeis.org/A078590)-/

namespace OeisA78590

/-- $a(1)=1, a(2)=1, a(n)=(2^{a(n-1)} + 1)/a(n-2)$. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => (2 ^ a (n + 2) + 1) / a (n + 1)

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by
  rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 9 := by
  rfl

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 171 := by
  rfl

/--
Are all terms integers?

No. Exact divisibility first fails at $n = 7$; the corresponding rational term has reduced
denominator $19$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a078590-counterexample/blob/3bdf1cee8e7e4cbc4fe83354e4be8ca1eee46de3/lean/OeisA78590CounterexampleFC.lean#L55-L61"]
theorem conjecture :
    answer(False) ↔ ∀ n : ℕ, 3 ≤ n → a (n - 2) ∣ 2 ^ a (n - 1) + 1 := by
  sorry

end OeisA78590
