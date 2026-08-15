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

open Real

/--
A208326: $c(n) = n + \lfloor nr/t \rfloor + \lfloor ns/t \rfloor$, where $\lfloor \cdot \rfloor$ is the floor function, $r=5$, $s=(1+\sqrt{5})/2$, and $t=1/s$.
-/
noncomputable def A208326 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n

  let term1_int : ℤ := Int.floor (n_r * r / t)
  let term2_int : ℤ := Int.floor (n_r * s / t)

  -- Sum the components in ℤ and convert the final result back to ℕ.
  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

@[simp] theorem a_one : A208326 1 = 11 := sorry
@[simp] theorem a_two : A208326 2 = 23 := sorry
@[simp] theorem a_three : A208326 3 = 34 := sorry
@[simp] theorem a_four : A208326 4 = 46 := sorry

/--
A207672: $a(n) = n + \lfloor ns/r \rfloor + \lfloor nt/r \rfloor$.
-/
noncomputable def A207672 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n

  let term1_int : ℤ := Int.floor (n_r * s / r)
  let term2_int : ℤ := Int.floor (n_r * t / r)

  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

/--
A207673: $b(n) = n + \lfloor nr/s \rfloor + \lfloor nt/s \rfloor$.
-/
noncomputable def A207673 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n

  let term1_int : ℤ := Int.floor (n_r * r / s)
  let term2_int : ℤ := Int.floor (n_r * t / s)

  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

/--
oeis_208326_conjecture_0: %C A208326 The sequences A207672, A207673, and A208326 partition the positive integers.
-/
theorem oeis_208326_conjecture_0 :
  ({n : ℕ | 0 < n} : Set ℕ) =
    (Set.range (A207672 ∘ Nat.succ)) ∪
    (Set.range (A207673 ∘ Nat.succ)) ∪
    (Set.range (A208326 ∘ Nat.succ)) ∧
  (Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A207673 ∘ Nat.succ) = ∅) ∧
  (Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = ∅) ∧
  (Set.range (A207673 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = ∅)
  := by sorry
