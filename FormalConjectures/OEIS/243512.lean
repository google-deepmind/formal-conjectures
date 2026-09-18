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
# Least index $i$ for which $\text{num}(\sigma_1(i)/i) - \text{den}(\sigma_1(i)/i) = n$

Let $A243473(i)$ be the difference between the numerator $p$ and the denominator $q$
when the abundancy index $\sigma_1(i) / i$ is written in lowest terms $p / q$.
The sequence $a(n)$ is the least positive integer $i$ such that $A243473(i) = n$,
or $0$ if no such index exists.

*References:*
- [A243512](https://oeis.org/A243512)
-/

namespace OeisA243512

open Finset

/-- Value of $A243473(i)$: numerator minus denominator of $\sigma_1(i) / i$ in lowest terms. -/
def a243473 (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : ℚ := (∑ d ∈ i.divisors, d : ℚ) / i
    (r.num - r.den).toNat

/-- Least positive integer $i$ such that $A243473(i) = n$, or $0$ if no such index exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {i : ℕ | 0 < i ∧ a243473 i = n}

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  exact IsLeast.csInf_eq ⟨by native_decide, fun x hx => hx.1⟩

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  refine IsLeast.csInf_eq ⟨by native_decide, fun x ⟨hx1, hx2⟩ => ?_⟩
  by_contra! h
  interval_cases x
  revert hx2; native_decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by
  refine IsLeast.csInf_eq ⟨by native_decide, fun x ⟨hx1, hx2⟩ => ?_⟩
  by_contra! h
  interval_cases x <;> revert hx2 <;> native_decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 9 := by
  refine IsLeast.csInf_eq ⟨by native_decide, fun x ⟨hx1, hx2⟩ => ?_⟩
  by_contra! h
  interval_cases x <;> revert hx2 <;> native_decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 14 := by
  refine IsLeast.csInf_eq ⟨by native_decide, fun x ⟨hx1, hx2⟩ => ?_⟩
  by_contra! h
  interval_cases x <;> revert hx2 <;> native_decide

/--
Motivated by the observation that some small numbers $(2, 12, 14, 18, \dots)$ occur only very late in
the recently added sequence A243473, but all numbers seem to appear sooner or later. (The definition
is completed by "$0$ if no such index exists" to guarantee well-definedness in absence of a proof,
but I conjecture that no such $0$ will ever occur.)
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) : a n ≠ 0 := by
  sorry

end OeisA243512
