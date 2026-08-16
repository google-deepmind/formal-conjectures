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

/-- Number of iterations required to turn $n$ into 1 in the Collatz process. -/
noncomputable def collatzSteps (n : ℕ) : ℕ :=
  if n = 0 then 0 else sInf {k : ℕ | (collatzStep^[k]) n = 1}

/-- The sequence $a(n) = \mathrm{A006577}(n+1) - \mathrm{A006577}(n)$ for $n > 0$. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else (collatzSteps (n + 1) : ℤ) - (collatzSteps n : ℤ)

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  have h1 : IsLeast {k : ℕ | (collatzStep^[k]) 1 = 1} 0 :=
    ⟨rfl, fun k _ => zero_le k⟩
  have h2 : IsLeast {k : ℕ | (collatzStep^[k]) 2 = 1} 1 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k; revert hk; decide
  have hs1 : collatzSteps 1 = 0 := by
    unfold collatzSteps; split <;> [omega; exact h1.csInf_eq]
  have hs2 : collatzSteps 2 = 1 := by
    unfold collatzSteps; split <;> [omega; exact h2.csInf_eq]
  unfold a
  split
  · omega
  · rw [show (1 + 1 : ℕ) = 2 from rfl, hs1, hs2]
    norm_num

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 6 := by
  have h2 : IsLeast {k : ℕ | (collatzStep^[k]) 2 = 1} 1 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k; revert hk; decide
  have h3 : IsLeast {k : ℕ | (collatzStep^[k]) 3 = 1} 7 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have hs2 : collatzSteps 2 = 1 := by
    unfold collatzSteps; split <;> [omega; exact h2.csInf_eq]
  have hs3 : collatzSteps 3 = 7 := by
    unfold collatzSteps; split <;> [omega; exact h3.csInf_eq]
  unfold a
  split
  · omega
  · rw [show (2 + 1 : ℕ) = 3 from rfl, hs2, hs3]
    norm_num

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = -5 := by
  have h3 : IsLeast {k : ℕ | (collatzStep^[k]) 3 = 1} 7 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have h4 : IsLeast {k : ℕ | (collatzStep^[k]) 4 = 1} 2 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have hs3 : collatzSteps 3 = 7 := by
    unfold collatzSteps; split <;> [omega; exact h3.csInf_eq]
  have hs4 : collatzSteps 4 = 2 := by
    unfold collatzSteps; split <;> [omega; exact h4.csInf_eq]
  unfold a
  split
  · omega
  · rw [show (3 + 1 : ℕ) = 4 from rfl, hs3, hs4]
    norm_num

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  have h4 : IsLeast {k : ℕ | (collatzStep^[k]) 4 = 1} 2 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have h5 : IsLeast {k : ℕ | (collatzStep^[k]) 5 = 1} 5 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have hs4 : collatzSteps 4 = 2 := by
    unfold collatzSteps; split <;> [omega; exact h4.csInf_eq]
  have hs5 : collatzSteps 5 = 5 := by
    unfold collatzSteps; split <;> [omega; exact h5.csInf_eq]
  unfold a
  split
  · omega
  · rw [show (4 + 1 : ℕ) = 5 from rfl, hs4, hs5]
    norm_num

/-- The set of positive indices $n$ for which $a(n) = v$. -/
def indices (v : ℤ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ a n = v}

/--
Conjecture 1: More than half of the terms are 0.
- _Ya-Ping Lu_, May 04 2024
-/
@[category research open, AMS 11]
theorem conjecture1 :
    1 / 2 < Filter.atTop.liminf (fun n : ℕ ↦
      (((Finset.Icc 1 n).filter (fun i ↦ a i = 0)).card : ℝ) / (n : ℝ)) := by
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

end OeisA153330
