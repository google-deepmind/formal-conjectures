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
# A108211

The sequence is defined by $a(n) = 16n^2 + 1$.

*References:*
- [A108211](https://oeis.org/A108211)
-/

namespace OeisA108211

/--
The primary defining sequence `a`.
`a n` is defined as $16n^2 + 1$.
-/
def a (n : ℕ) : ℕ := 16 * n ^ 2 + 1

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_1 : a 1 = 17 := by decide

@[category test, AMS 11]
lemma test_a_2 : a 2 = 65 := by decide

@[category test, AMS 11]
lemma test_a_3 : a 3 = 145 := by decide

@[category test, AMS 11]
lemma test_a_4 : a 4 = 257 := by decide

@[category test, AMS 11]
lemma test_a_5 : a 5 = 401 := by decide

open Real

/--
Conjecture: a(n) = floor(1/(1/(4*n) - log(2) + 1/(n+1) + 1/(n+2) + ... + 1/(2*n))).
-/
@[category research open, AMS 11]
theorem main_conjecture (n : ℕ) (hn : n > 0) :
    (a n : ℝ) = (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + Finset.sum (Finset.Icc (n + 1) (2 * n)) fun k => (k : ℝ)⁻¹) ⌋ : ℝ) := by
  sorry

end OeisA108211
