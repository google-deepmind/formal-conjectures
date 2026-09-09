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
# Difference between first odd semiprime $> 2^n$ and $2^n$

*References:*
- [A114137](https://oeis.org/A114137)
-/

namespace OeisA114137
open Nat

/--
The primary defining sequence `a`.
$a(n)$ is the difference between first odd semiprime > $2^n$ and $2^n$.
$$a(n) = \min \{s \mid s > 2^n \text{ and } s \text{ is an odd semiprime}\} - 2^n$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  let m := 2^n
  let s : Set ℕ := { s | s > m ∧ s.IsSemiprime ∧ Odd s }
  sInf s - m

@[category API, AMS 11]
lemma a_eq_of (n val : ℕ)
  (h_mem : val.IsSemiprime ∧ Odd val)
  (h_gt : 2^n < val)
  (h_min : ∀ x, 2^n < x → x < val → ¬ (x.IsSemiprime ∧ Odd x)) :
  a n = val - 2^n := by
  change sInf { s | s > 2^n ∧ s.IsSemiprime ∧ Odd s } - 2^n = val - 2^n
  have h_S : sInf { s | s > 2^n ∧ s.IsSemiprime ∧ Odd s } = val := by
    apply IsLeast.csInf_eq
    constructor
    · exact ⟨h_gt, h_mem⟩
    · rintro x ⟨hx1, hx2⟩
      by_contra! h
      exact h_min x hx1 h hx2
  rw [h_S]

@[category test, AMS 11]
theorem a_1 : a 1 = 7 := by
  apply a_eq_of 1 9 (by native_decide) (by norm_num)
  intro x h1 h2
  interval_cases x <;> native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by
  apply a_eq_of 2 9 (by native_decide) (by norm_num)
  intro x h1 h2
  interval_cases x <;> native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  apply a_eq_of 3 9 (by native_decide) (by norm_num)
  intro x h1 h2
  interval_cases x

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  apply a_eq_of 4 21 (by native_decide) (by norm_num)
  intro x h1 h2
  interval_cases x <;> native_decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  apply a_eq_of 5 33 (by native_decide) (by norm_num)
  intro x h1 h2
  interval_cases x

/--
In this powers of 2 sequence, does 1 occur infinitely often?
-/
@[category research open, AMS 11]
theorem conjecture1 :
  answer(sorry) ↔ Set.Infinite {n : ℕ | a n = 1} := by
  sorry

/--
Does every odd number occur?
-/
@[category research open, AMS 11]
theorem conjecture2 :
  answer(sorry) ↔ ∀ k : ℕ, Odd k → ∃ n : ℕ, a n = k := by
  sorry

end OeisA114137
