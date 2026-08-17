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
# Collatz step differences

Differences in adjacent elements of the sequence quantifying the steps needed for $n$ to
converge to 1 in the Collatz Conjecture.
$$a(n) = \mathrm{A006577}(n+1) - \mathrm{A006577}(n)$$
for $n > 0$.

*References:*
- [A153330](https://oeis.org/A153330)-/

namespace OeisA153330

/-- Single step of the Collatz mapping. -/
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

open Classical in
/-- Number of iterations required to turn $n$ into 1 in the Collatz process,
or `none` if $n$ does not terminate. -/
noncomputable def collatzSteps (n : ℕ) : Option ℕ :=
  if n = 0 then none
  else if ∃ k : ℕ, (collatzStep^[k]) n = 1 then
    some (sInf {k : ℕ | (collatzStep^[k]) n = 1})
  else
    none

open Classical in
/-- The sequence $a(n) = \mathrm{A006577}(n+1) - \mathrm{A006577}(n)$ for $n > 0$,
or `none` if either $n$ or $n+1$ does not terminate. -/
noncomputable def a (n : ℕ) : Option ℤ :=
  if n = 0 then none
  else
    match collatzSteps (n + 1), collatzSteps n with
    | some s2, some s1 => some (s2 - s1)
    | _, _ => none

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = none := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = some 1 := by
  have h1 : IsLeast {k : ℕ | (collatzStep^[k]) 1 = 1} 0 :=
    ⟨rfl, fun k _ => zero_le k⟩
  have h2 : IsLeast {k : ℕ | (collatzStep^[k]) 2 = 1} 1 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k; revert hk; decide
  have hs1 : collatzSteps 1 = some 0 := by
    have h : ∃ k, (collatzStep^[k]) 1 = 1 := ⟨0, h1.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h1.csInf_eq]
  have hs2 : collatzSteps 2 = some 1 := by
    have h : ∃ k, (collatzStep^[k]) 2 = 1 := ⟨1, h2.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h2.csInf_eq]
  rw [a, if_neg (by omega), hs2, hs1]; rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = some 6 := by
  have h2 : IsLeast {k : ℕ | (collatzStep^[k]) 2 = 1} 1 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k; revert hk; decide
  have h3 : IsLeast {k : ℕ | (collatzStep^[k]) 3 = 1} 7 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have hs2 : collatzSteps 2 = some 1 := by
    have h : ∃ k, (collatzStep^[k]) 2 = 1 := ⟨1, h2.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h2.csInf_eq]
  have hs3 : collatzSteps 3 = some 7 := by
    have h : ∃ k, (collatzStep^[k]) 3 = 1 := ⟨7, h3.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h3.csInf_eq]
  rw [a, if_neg (by omega), hs3, hs2]; rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = some (-5) := by
  have h3 : IsLeast {k : ℕ | (collatzStep^[k]) 3 = 1} 7 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have h4 : IsLeast {k : ℕ | (collatzStep^[k]) 4 = 1} 2 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have hs3 : collatzSteps 3 = some 7 := by
    have h : ∃ k, (collatzStep^[k]) 3 = 1 := ⟨7, h3.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h3.csInf_eq]
  have hs4 : collatzSteps 4 = some 2 := by
    have h : ∃ k, (collatzStep^[k]) 4 = 1 := ⟨2, h4.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h4.csInf_eq]
  rw [a, if_neg (by omega), hs4, hs3]; rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = some 3 := by
  have h4 : IsLeast {k : ℕ | (collatzStep^[k]) 4 = 1} 2 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have h5 : IsLeast {k : ℕ | (collatzStep^[k]) 5 = 1} 5 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have hs4 : collatzSteps 4 = some 2 := by
    have h : ∃ k, (collatzStep^[k]) 4 = 1 := ⟨2, h4.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h4.csInf_eq]
  have hs5 : collatzSteps 5 = some 5 := by
    have h : ∃ k, (collatzStep^[k]) 5 = 1 := ⟨5, h5.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h5.csInf_eq]
  rw [a, if_neg (by omega), hs5, hs4]; rfl

/-- The set of positive indices $n$ for which $a(n) = v$. -/
def indices (v : ℤ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ a n = some v}

/--
Conjecture 1: More than half of the terms are 0.
- _Ya-Ping Lu_, May 04 2024
-/
@[category research open, AMS 11]
theorem conjecture1 :
    1 / 2 < Filter.atTop.liminf (fun n : ℕ ↦
      (((Finset.Icc 1 n).filter (fun i ↦ a i = some 0)).card : ℝ) / (n : ℝ)) := by
  sorry

/--
Conjecture 2: 1, 6 and 16 appear only once and 3 appears twice in the sequence,
i.e., $a(1) = 1$, $a(2) = 6$, $a(4) = a(5) = 3$, and $a(8) = 16$.
- _Ya-Ping Lu_, May 04 2024
-/
@[category research open, AMS 11]
theorem conjecture2 :
    indices 1 = {1} ∧
    indices 6 = {2} ∧
    indices 16 = {8} ∧
    indices 3 = {4, 5} := by
  sorry

/--
Conjecture 3 (Ya-Ping Lu, 2024):
Except 1, 3 and 6, the absolute value of all terms can be written as $5x + 8y$ for $x, y \in \mathbb{N}$.
(Note: in the OEIS comment, "x and y are integers" means $x$ and $y$ have the same sign,
i.e., $|v| = 5x + 8y$ with $x, y \ge 0$, since every integer is a $\mathbb{Z}$-linear combination of 5 and 8).
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (v : ℤ) (hn : 0 < n) (ha : a n = some v)
    (hv : v ≠ 1 ∧ v ≠ 3 ∧ v ≠ 6) :
    ∃ x y : ℕ, v.natAbs = 5 * x + 8 * y := by
  sorry

/--
Conjecture 4 (Ya-Ping Lu, 2024):
The ratio of the number of terms with value $m$ to that of $-m$ approaches 1 as $n \to \infty$,
for any $m \notin \{1, 3, 6, 16\}$.
-/
@[category research open, AMS 11]
theorem conjecture4 (m : ℤ) (hm : m ≠ 1 ∧ m ≠ 3 ∧ m ≠ 6 ∧ m ≠ 16) :
    Filter.atTop.Tendsto
      (fun n : ℕ ↦
        (((Finset.Icc 1 n).filter (fun i ↦ a i = some m)).card : ℝ) /
        (((Finset.Icc 1 n).filter (fun i ↦ a i = some (-m))).card : ℝ))
      (nhds 1) := by
  sorry

end OeisA153330
