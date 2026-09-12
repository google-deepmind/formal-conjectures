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
# Erdős Problem 864

*References:*
- [erdosproblems.com/864](https://www.erdosproblems.com/864)
- [erdosproblems.com/840](https://www.erdosproblems.com/840)
-/

open Asymptotics Filter Finset

namespace Erdos864

/-- The number of solutions of `n = a + b` with `a ≤ b` in `A`. -/
def numSumReps (A : Finset ℕ) (n : ℕ) : ℕ :=
  ((A ×ˢ A).filter fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n).card

/--
There is at most one `n` with more than one solution to `n = a + b` (`a ≤ b` in `A`).
-/
def AlmostUniqueSums (A : Finset ℕ) : Prop :=
  {n | 1 < numSumReps A n}.encard ≤ 1

/-- Maximal size of such a subset of `{1, …, N}`. -/
noncomputable def maxSize (N : ℕ) : ℕ :=
  sSup ((·.card) '' {A : Finset ℕ | A ⊆ Icc 1 N ∧ AlmostUniqueSums A})

/-- The number of solutions of `n = a - b` with `a, b ∈ A` and `n > 0`. -/
def numDiffReps (A : Finset ℕ) (n : ℕ) : ℕ :=
  ((A ×ˢ A).filter fun p => p.1 = p.2 + n).card

/-- At most one positive `n` has more than one difference representation. -/
def AlmostUniqueDiffs (A : Finset ℕ) : Prop :=
  {n | 0 < n ∧ 1 < numDiffReps A n}.encard ≤ 1

/-- Maximal size for the difference analogue. -/
noncomputable def maxDiffSize (N : ℕ) : ℕ :=
  sSup ((·.card) '' {A : Finset ℕ | A ⊆ Icc 1 N ∧ AlmostUniqueDiffs A})

/--
Let $A\subseteq \{1,\ldots N\}$ be a set such that there exists at most one $n$ with more than
one solution to $n=a+b$ (with $a\leq b\in A$). Estimate the maximal possible size of
$\lvert A\rvert$ - in particular, is it true that
$$\lvert A\rvert \leq (1+o(1))\frac{2}{\sqrt{3}}N^{1/2}?$$
-/
@[category research open, AMS 5]
theorem erdos_864 : answer(sorry) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (maxSize N : ℝ) ≤ (1 + ε) * (2 / Real.sqrt 3) * (N : ℝ) ^ (1 / 2 : ℝ) := by
  sorry

/--
A problem of Erdős and Freud, who prove that
$$\lvert A\rvert \geq (1+o(1))\frac{2}{\sqrt{3}}N^{1/2}.$$
This is shown by taking a genuine Sidon set $B\subset [1,N/3]$ of size $\sim N^{1/2}/\sqrt{3}$
and taking the union with $\{N-b : b\in B\}$.
-/
@[category research solved, AMS 5]
theorem erdos_864.variants.lower_bound :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (1 - ε) * (2 / Real.sqrt 3) * (N : ℝ) ^ (1 / 2 : ℝ) ≤ (maxSize N : ℝ) := by
  sorry

/--
For the analogous question with $n=a-b$ they prove that $\lvert A\rvert\sim N^{1/2}$.
-/
@[category research solved, AMS 5]
theorem erdos_864.variants.differences :
    (fun N => (maxDiffSize N : ℝ)) ~[atTop] fun N => (N : ℝ) ^ (1 / 2 : ℝ) := by
  sorry

end Erdos864
