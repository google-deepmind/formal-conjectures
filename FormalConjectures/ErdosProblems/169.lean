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
# Erdős Problem 169

*Reference:* [erdosproblems.com/169](https://www.erdosproblems.com/169)
-/

@[expose] public section

open scoped ENNReal Topology

namespace Erdos169

/--
The set of $N$ such that every $2$-colouring of $\{1, \dots, N\}$ contains a monochromatic
$k$-term arithmetic progression.
-/
def monoAPGuaranteeSet (k : ℕ) : Set ℕ :=
  {N | ∀ coloring : Finset.Icc 1 N → Fin 2, ContainsMonoAPofLength coloring k}

/-- The two-colour van der Waerden number $W(k)$, defined as in Erdős Problem 138. -/
noncomputable def W (k : ℕ) : ℕ := sInf (monoAPGuaranteeSet k)

/-- The sum of the reciprocals of the elements of $A$, allowing $\infty$. -/
noncomputable def reciprocalSum (A : Set ℕ) : ℝ≥0∞ :=
  ∑' n : A, (n.val : ℝ≥0∞)⁻¹

/-- The supremum of reciprocal sums over sets of positive integers containing no
$k$-term arithmetic progression. -/
noncomputable def f (k : ℕ) : ℝ≥0∞ :=
  ⨆ (A : Set ℕ) (_ : A ⊆ Set.Ioi 0) (_ : A.IsAPOfLengthFree k), reciprocalSum A

@[category API, AMS 5 11]
lemma reciprocalSum_le_f {A : Set ℕ} {k : ℕ}
    (hpos : A ⊆ Set.Ioi 0) (hfree : A.IsAPOfLengthFree k) : reciprocalSum A ≤ f k := by
  exact le_iSup_of_le A (le_iSup_of_le hpos (le_iSup_of_le hfree le_rfl))

/--
Let $k\geq 3$ and $f(k)$ be the supremum of $\sum_{n\in A}\frac{1}{n}$ as $A$ ranges over
all sets of positive integers which do not contain a $k$-term arithmetic progression.
Is
$$\lim_{k\to\infty}\frac{f(k)}{\log W(k)}=\infty$$
where $W(k)$ is the van der Waerden number?
-/
@[category research open, AMS 5 11]
theorem erdos_169 : answer(sorry) ↔
    Filter.Tendsto (fun k : ℕ =>
      f (k + 3) / ENNReal.ofReal (Real.log (W (k + 3) : ℝ)))
      Filter.atTop (𝓝 (⊤ : ℝ≥0∞)) := by
  sorry

/--
For every $\epsilon>0$ and $k\geq 3$, if $A$ is a set of positive integers without a
$k$-term arithmetic progression and $\min(A)$ is sufficiently large in terms of $\epsilon$
and $k$, is $\sum_{n\in A}\frac{1}{n}<\epsilon$?
-/
@[category research open, AMS 5 11]
theorem erdos_169.variants.uniform_tail : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 3 ≤ k →
      ∃ N : ℕ, ∀ A : Set ℕ, A ⊆ Set.Ioi 0 → A.IsAPOfLengthFree k →
        (∀ n ∈ A, N ≤ n) → reciprocalSum A < ENNReal.ofReal ε := by
  sorry

end Erdos169
