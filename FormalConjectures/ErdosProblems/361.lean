/-
Copyright 2025 The Formal Conjectures Authors.

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

/-!
# Erdős Problem 361

*Reference:* [erdosproblems.com/361](https://www.erdosproblems.com/361)
-/

open Filter

/--
Let $c>0$ and $n$ be some large integer. What is the size of the largest
$A\subseteq \{1,\ldots,\lfloor cn\rfloor\}$ such that $n$ is not a sum of a subset of $A$?
Does this depend on $n$ in an irregular way?
-/
@[category research open, AMS 11]
theorem erdos_361.bigO
    (c : ℝ) (hc : 0 < c)
    (A : ℕ → ℕ)
    (hA : ∀ c n, A n = ((Finset.Icc 1 ⌊c * n⌋₊).powerset.filter
      (fun B ↦ n ≠ ∑ a ∈ B, a)).sup Finset.card) :
    (fun n ↦ (A n : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Let $c>0$ and $n$ be some large integer. What is the size of the largest
$A\subseteq \{1,\ldots,\lfloor cn\rfloor\}$ such that $n$ is not a sum of a subset of $A$?
Does this depend on $n$ in an irregular way?
-/
@[category research open, AMS 11]
theorem erdos_361.bigTheta
    (c : ℝ) (hc : 0 < c)
    (A : ℕ → ℕ)
    (hA : ∀ c n, A n = ((Finset.Icc 1 ⌊c * n⌋₊).powerset.filter
      (fun B ↦ n ≠ ∑ a ∈ B, a)).sup Finset.card) :
    (fun n ↦ (A n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Let $c>0$ and $n$ be some large integer. What is the size of the largest
$A\subseteq \{1,\ldots,\lfloor cn\rfloor\}$ such that $n$ is not a sum of a subset of $A$?
Does this depend on $n$ in an irregular way?
-/
@[category research open, AMS 11]
theorem erdos_361.smallO
    (c : ℝ) (hc : 0 < c)
    (A : ℕ → ℕ)
    (hA : ∀ c n, A n = ((Finset.Icc 1 ⌊c * n⌋₊).powerset.filter
      (fun B ↦ n ≠ ∑ a ∈ B, a)).sup Finset.card) :
    (fun n ↦ (A n : ℝ)) =o[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry
