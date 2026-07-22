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
# A102722 Conjecture

Given $n$, sum all division remainders $\{n/k\}$, with $k=1,\dots,n$.
The value $a(n)$ is given by the floor of that sum. Note that $\{x\}:=x-[x]$.
Conjecture: a(n) ~ (1-EulerGamma)n.

*References:*
- [A102722](https://oeis.org/A102722)
-/

namespace OeisA102722

open BigOperators Finset Int

/-- The primary defining sequence `a`.
a n is the floor of the sum of all division remainders $\{n/k\}$, with $k=1,\dots,n$.
$$a(n) = \left\lfloor \sum_{k=1}^n \left\{ \frac{n}{k} \right\} \right\rfloor$$ -/
noncomputable def a (n : ℕ) : ℕ :=
  let sum_of_fract_parts : ℝ :=
    (Icc 1 n).sum fun k : ℕ =>
      -- Int.fract is the fractional part function {x}.
      fract ((n : ℝ) / (k : ℝ))
  (floor sum_of_fract_parts).toNat

@[category API, AMS 11]
lemma a_sum_1 (f : ℕ → ℝ) : (Icc 1 1).sum f = f 1 := by
  have h : Icc 1 1 = {1} := rfl
  rw [h, Finset.sum_singleton]

@[category API, AMS 11]
lemma a_sum_2 (f : ℕ → ℝ) : (Icc 1 2).sum f = f 1 + f 2 := by
  have h : Icc 1 2 = {1, 2} := rfl
  rw [h, Finset.sum_insert (by decide), Finset.sum_singleton]

@[category API, AMS 11]
lemma a_sum_3 (f : ℕ → ℝ) : (Icc 1 3).sum f = f 1 + f 2 + f 3 := by
  have h : Icc 1 3 = {1, 2, 3} := rfl
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

@[category API, AMS 11]
lemma a_sum_4 (f : ℕ → ℝ) : (Icc 1 4).sum f = f 1 + f 2 + f 3 + f 4 := by
  have h : Icc 1 4 = {1, 2, 3, 4} := rfl
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

@[category API, AMS 11]
lemma a_sum_5 (f : ℕ → ℝ) : (Icc 1 5).sum f = f 1 + f 2 + f 3 + f 4 + f 5 := by
  have h : Icc 1 5 = {1, 2, 3, 4, 5} := rfl
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

macro "eval_a" : tactic => `(tactic| (
  delta a
  simp only [a_sum_1, a_sum_2, a_sum_3, a_sum_4, a_sum_5]
  norm_num
))

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by eval_a

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by eval_a

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by eval_a

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by eval_a

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by eval_a

/-- A102722 Conjecture: a(n) ~ (1-EulerGamma)n. -/
@[category research open, AMS 11]
theorem conjecture :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => (1 - Real.eulerMascheroniConstant) * (n : ℝ)) := by
  sorry

end OeisA102722
