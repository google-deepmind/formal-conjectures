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
# Cuban Primes

OEIS A002407 lists the primes that are differences of two consecutive positive cubes. The
sequence is conjectured to be infinite.

*References:*
- [OEIS A002407](https://oeis.org/A002407)
-/

namespace OeisA2407

/-- A natural number is in A002407 when it is prime and is the difference of two consecutive
positive cubes. The addition equality avoids truncated subtraction in `ℕ`. -/
def A (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k > 0, p + k ^ 3 = (k + 1) ^ 3

@[category test, AMS 11]
theorem a_7 : A 7 := by
  refine ⟨by norm_num, 1, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem a_19 : A 19 := by
  refine ⟨by norm_num, 2, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem a_37 : A 37 := by
  refine ⟨by norm_num, 3, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem a_61 : A 61 := by
  refine ⟨by norm_num, 4, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem a_127 : A 127 := by
  refine ⟨by norm_num, 6, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem not_a_91 : ¬ A 91 := by
  norm_num [A, Nat.prime_def_lt]

/--
This sequence is believed to be infinite.
-/
@[category research open, AMS 11]
theorem conjecture : {p : ℕ | A p}.Infinite := by
  sorry

end OeisA2407
