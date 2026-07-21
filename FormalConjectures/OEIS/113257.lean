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

/-!
# Ascending descending base exponent transform of squares

a n is the sum from i=1 to n of (i^2)^((n-i+1)^2).

*References:*
- [A113257](https://oeis.org/A113257)
-/

namespace OeisA113257

/-- a n is the ascending descending base exponent transform of squares -/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.Icc 1 n) (fun i ↦ (i ^ 2) ^ ((n - i + 1) ^ 2))

@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
lemma test_a_2 : a 2 = 5 := by decide

@[category test, AMS 11]
lemma test_a_3 : a 3 = 266 := by decide

@[category test, AMS 11]
lemma test_a_4 : a 4 = 268722 := by decide

@[category test, AMS 11]
lemma test_a_5 : a 5 = 4682453347 := by decide

/--
The smallest prime in this sequence is a(2) = 5. What is the next prime?
-/
@[category research open, AMS 11]
theorem conjecture1 :
    answer(sorry) = a (sInf {n : ℕ | 2 < n ∧ Nat.Prime (a n)}) := by
  sorry

/--
What is the first square value after 1?
-/
@[category research open, AMS 11]
theorem conjecture2 :
    answer(sorry) = a (sInf {n : ℕ | 1 < n ∧ ∃ k, a n = k ^ 2}) := by
  sorry

end OeisA113257
