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
module

public import FormalConjecturesUtil

/-!
# Twin primes of the form $(3^n - k) 2^n \pm 1$

For $n > 0$, $a(n)$ is the smallest nonnegative integer $k$ such that $(3^n - k) 2^n - 1$ and
$(3^n - k) 2^n + 1$ form a twin prime pair.

*References:*
- [A214497](https://oeis.org/A214497)
-/

@[expose] public section

namespace OeisA214497

/-- Smallest $k \ge 0$ such that $(3^n - k) 2^n - 1$ and $(3^n - k) 2^n + 1$
are both prime, or `none` if no such $k$ exists. -/
def a (n : ℕ) : Option ℕ :=
  (List.range (3 ^ n)).find? fun k =>
    Nat.Prime ((3 ^ n - k) * 2 ^ n - 1) && Nat.Prime ((3 ^ n - k) * 2 ^ n + 1)

@[category test, AMS 11]
theorem a_1 : a 1 = some 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = some 6 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = some 3 := by
  rw [a, List.find?_eq_some_iff_getElem]
  refine ⟨?_, 3, by simp, rfl, fun j hj => ?_⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    norm_num
  · simp only [List.getElem_range]
    interval_cases j <;> norm_num

@[category test, AMS 11]
theorem a_4 : a 4 = some 9 := by
  rw [a, List.find?_eq_some_iff_getElem]
  refine ⟨?_, 9, by simp, rfl, fun j hj => ?_⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    norm_num
  · simp only [List.getElem_range]
    interval_cases j <;> norm_num

@[category test, AMS 11]
theorem a_5 : a 5 = some 9 := by
  rw [a, List.find?_eq_some_iff_getElem]
  refine ⟨?_, 9, by simp, rfl, fun j hj => ?_⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    norm_num
  · simp only [List.getElem_range]
    interval_cases j <;> norm_num

/--
Conjecture: There is always one such $k$ for each $n > 0$ such that
$(3^n - k) 2^n - 1$ and $(3^n - k) 2^n + 1$ are a twin prime pair.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) : (a n).isSome := by
  sorry

end OeisA214497
