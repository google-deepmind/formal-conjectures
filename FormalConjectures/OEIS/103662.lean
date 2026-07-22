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
# Smallest power with base>1 and exponent n whose decimal representation doesn't contain the digit 0

A103662: Smallest power with base>1 and exponent $n$ whose decimal representation doesn't contain the digit 0.
For statistical reasons it is conjectured that the sequence is finite.
Also it is conjectured that $a(40)$ does not exist (i.e. the sequence is empty for $n=40$).

*References:*
- [A103662](https://oeis.org/A103662)
-/

namespace OeisA103662

open Nat List Set

/--
A helper predicate: $b^n$ is a power with base $>1$ whose decimal representation does not contain the digit 0.
We assume $n$ is the exponent, $n \ge 1$.
-/
def is_valid_zeroless_power (n b : ℕ) : Prop :=
  b > 1 ∧ 0 ∉ digits 10 (b ^ n)

/--
The primary defining sequence `a`.
`a n` is the smallest power with base $>1$ and exponent $n$ whose decimal representation doesn't contain the digit 0.
$$a(n) = (\min \{ b \in \mathbb{N} \mid b > 1, \text{decimal representation of } b^n \text{ contains no digit } 0 \})^n$$
If no such base exists, `sInf` of an empty set of naturals returns 0, so `a n = 0`.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let smallest_base := sInf { b | is_valid_zeroless_power n b }
  smallest_base ^ n

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_0 : a 0 = 1 := by
  constructor

@[category test, AMS 11]
lemma test_a_1 : a 1 = 2 := by
  simp_all[a]
  norm_num[Iff,is_valid_zeroless_power]
  exact ( IsLeast.csInf_eq ⟨.symm (by norm_num), fun and => And.left⟩)

@[category test, AMS 11]
lemma test_a_2 : a 2 = 4 := by
  norm_num[a]
  delta is_valid_zeroless_power
  exact (congr_arg) (.^2) (IsLeast.csInf_eq ⟨.symm (by norm_num), fun and=>And.left⟩)

@[category test, AMS 11]
lemma test_a_3 : a 3 = 8 := by
  norm_num[a]
  delta is_valid_zeroless_power
  exact (.trans (by rw [IsLeast.csInf_eq (by use ⟨by constructor,by norm_num⟩, fun and' => And.left)]) ( (by constructor)))

/--
For statistical reasons it is conjectured that the sequence is finite.
This is formalized as the assertion that for large enough $n$, no valid zeroless power exists,
which in our definition results in $a(n) = 0$.
-/
@[category research open, AMS 11]
theorem main_conjecture : ∃ N : ℕ, ∀ n : ℕ, n > N → a n = 0 := by
  sorry

/--
a(40), if it exists, is not known.

This claim is rooted in the finiteness conjecture. The most direct mathematical expression of the open problem concerning $a(40)$ is the negation of the existence of a valid base.
-/
@[category research open, AMS 11]
theorem main_conjecture.variants.a_40 :
  ¬ ∃ (b : ℕ), is_valid_zeroless_power 40 b := by
  sorry

end OeisA103662
