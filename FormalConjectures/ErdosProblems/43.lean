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

/-!
# Erdős Problem 43

*Reference:* [erdosproblems.com/43](https://www.erdosproblems.com/43)
-/

open scoped Pointwise

namespace Erdos43

/--
Let $f(N)$ be the maximum possible size of a Sidon set in $\{1,\ldots,N\}$.
-/
noncomputable abbrev f (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)

/--
If $A$ and $B$ are Sidon sets in $\{1,\ldots,N\}$ with
$(A-A)\cap(B-B)=\{0\}$, is it true that
$$\binom{\lvert A\rvert}{2}+\binom{\lvert B\rvert}{2}\leq\binom{f(N)}{2}+O(1)?$$

The answer is no; the Erdős Problems page notes that this follows from the solution to
Erdős Problem 42.
-/
@[category research solved, AMS 5 11]
theorem erdos_43.parts.i : answer(False) ↔
    ∃ C : ℝ, ∀ᶠ N in Filter.atTop, ∀ (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon (A : Set ℕ) →
      IsSidon (B : Set ℕ) →
      (A - A) ∩ (B - B) = {0} →
      ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) ≤ ((f N).choose 2 : ℝ) + C := by
  sorry

/--
If $A$ and $B$ are equal-sized Sidon sets in $\{1,\ldots,N\}$ with
$(A-A)\cap(B-B)=\{0\}$, can the bound be improved to
$$\binom{\lvert A\rvert}{2}+\binom{\lvert B\rvert}{2}
    \leq (1-c+o(1))\binom{f(N)}{2}$$
for some constant $c>0$?

The answer is no; the Erdős Problems page records a negative answer due to Barreto.
-/
@[category research solved, AMS 5 11]
theorem erdos_43.parts.ii : answer(False) ↔
    ∃ᵉ (c > 0), ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ N in Filter.atTop, ∀ (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon (A : Set ℕ) →
      IsSidon (B : Set ℕ) →
      A.card = B.card →
      (A - A) ∩ (B - B) = {0} →
      ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) ≤
        (1 - c + o N) * ((f N).choose 2 : ℝ) := by
  sorry

end Erdos43
