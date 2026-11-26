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
# Erdős Problem 432

*References:*
- [erdosproblems.com/432](https://www.erdosproblems.com/432)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathematique (1980), p. 85.
-/

@[expose] public section

namespace Erdos432

open Filter
open scoped Pointwise

/-- The number of distinct elements of $A+B$ in $\{1,\ldots,n\}$. -/
noncomputable def sumsetCounting (A B : Set ℕ) (n : ℕ) : ℕ :=
  ((A + B) ∩ Set.Icc 1 n).ncard

/-- The counting function is zero at zero. -/
@[category test, AMS 11]
theorem sumsetCounting_zero (A B : Set ℕ) : sumsetCounting A B 0 = 0 := by
  simp [sumsetCounting]

/-- An empty summand gives an empty sumset. -/
@[category test, AMS 11]
theorem sumsetCounting_empty_left (B : Set ℕ) (n : ℕ) :
    sumsetCounting ∅ B n = 0 := by
  simp [sumsetCounting]

/--
Let $A,B\subseteq \mathbb{N}$ be two infinite sets. How dense can $A+B$ be if all elements
of $A+B$ are pairwise relatively prime?

Asked by Straus, inspired by a problem of Ostmann (see Problem 431).

Here density is measured by the counting function $|(A+B)\cap\{1,\ldots,n\}|$.
The answer specifies the attainable asymptotic orders, up to positive constant factors,
represented by eventually nonnegative functions $f\colon\mathbb{N}\to\mathbb{R}$.
-/
@[category research open, AMS 11]
theorem erdos_432 :
    (answer(sorry) : Set (ℕ → ℝ)) =
      {f | (∀ᶠ n in atTop, 0 ≤ f n) ∧
        ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧ (A + B).Pairwise Nat.Coprime ∧
          (fun n ↦ (sumsetCounting A B n : ℝ)) =Θ[atTop] f} := by
  sorry

end Erdos432
