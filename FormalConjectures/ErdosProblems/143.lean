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
# Erdős Problem 143

*Reference:* [erdosproblems.com/143](https://www.erdosproblems.com/143)
-/

open Filter Finset
open scoped Topology

/--
Let $A \subseteq (1, \infty)$ be a countably infinite set such that for all $x\neq y\in A$ and
integers $k \geq 1$ we have $|kx - y| \geq 1$.
-/
def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ (Set.Ioi (1 : ℝ))) ∧ Set.Infinite A ∧ Set.Countable A ∧
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∀ k ≥ (1 : ℕ), 1 ≤ |k * x - y|))

/--
Does this imply that
$$
\liminf \frac{|A \cap [1,x]|}{x} = 0?
$$
-/
@[category research open, AMS 11]
theorem erdos_143.parts.i : (∀ (A : Set ℝ), WellSeparatedSet A →
    liminf (fun x => (A ∩ (Set.Icc 1 x)).ncard / x) atTop = 0) ↔ answer(sorry) := by
  sorry

/--
Or
$$
\sum_{x \in A} \frac{1}{x \log x} < \infty,
$$
-/
@[category research open, AMS 11]
theorem erdos_143.parts.ii (A : Set ℝ) (h : WellSeparatedSet A):
    ∃ (s : ℝ),
      Tendsto (fun n ↦ ∑ x ∈ range n, 1 / (x * Real.log x)) atTop (𝓝 s) := by
  sorry


-- TODO(firsching): add the two other conjectures.
/-
$$
\sum_{\substack{x < n \\ x \in A}} \frac{1}{x} = o(\log n)?
$$

Perhaps even

$$
\sum_{\substack{x < n \\ x \in A}} \frac{1}{x} \ll \frac{\log x}{\sqrt{\log \log x}}?
$$
-/
