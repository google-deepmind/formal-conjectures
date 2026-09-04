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
# Emirps

An emirp is a prime whose decimal reversal is a different prime. It is unknown whether there are
infinitely many emirps.

*References:*
* [Wikipedia, Emirp](https://en.wikipedia.org/wiki/Emirp)
* [OEIS A006567](https://oeis.org/A006567)
-/

namespace Emirp

/-- Reverse the base-ten digits of a natural number. -/
def reverse10 (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- A natural number is an emirp if it and its distinct decimal reversal are both prime. -/
def IsEmirp (p : ℕ) : Prop :=
  p.Prime ∧ (reverse10 p).Prime ∧ reverse10 p ≠ p

@[category test, AMS 11]
theorem reverse10_13 : reverse10 13 = 31 := by
  norm_num [reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem reverse10_17 : reverse10 17 = 71 := by
  norm_num [reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem reverse10_120 : reverse10 120 = 21 := by
  norm_num [reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem a_13 : IsEmirp 13 := by
  norm_num [IsEmirp, reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem a_17 : IsEmirp 17 := by
  norm_num [IsEmirp, reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem a_31 : IsEmirp 31 := by
  norm_num [IsEmirp, reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem a_37 : IsEmirp 37 := by
  norm_num [IsEmirp, reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem not_a_11 : ¬ IsEmirp 11 := by
  norm_num [IsEmirp, reverse10, Nat.ofDigits]

/-- [Wikipedia's article on emirps](https://en.wikipedia.org/wiki/Emirp) states: "It is not known
whether there are infinitely many emirps." -/
@[category research open, AMS 11]
theorem infinitude_question :
    answer(sorry) ↔ {p : ℕ | IsEmirp p}.Infinite := by
  sorry

end Emirp
