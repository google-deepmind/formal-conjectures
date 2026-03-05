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
# Erdős Problem 254

If $A \subseteq \mathbb{N}$ satisfies $|A \cap [1, 2x]| - |A \cap [1, x]| \to \infty$ and
$\sum_{n \in A} \|n\theta\| = \infty$ for every irrational $\theta$, then every sufficiently large
integer is the sum of distinct elements of $A$.

*Reference:* [erdosproblems.com/254](https://www.erdosproblems.com/254)

[Er61] Erdős, P., _Some unsolved problems_, Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
6, 221-254.
-/

open Set Filter BigOperators Classical

namespace Erdos254

/-- The distance of a real number $x$ from the nearest integer. -/
noncomputable def distNearestInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/--
Erdős Problem #254 [Er61]:
Let $A \subseteq \mathbb{N}$ be such that
$|A \cap [1, 2x]| - |A \cap [1, x]| \to \infty$ as $x \to \infty$, and
$\sum_{n \in A} \|n\theta\| = \infty$ for every $\theta \in (0,1)$, where $\|x\|$ denotes the
distance of $x$ from the nearest integer. Then every sufficiently large integer is the sum of
distinct elements of $A$.
-/
@[category research open, AMS 11]
theorem erdos_254
    (A : Set ℕ)
    (hgrowth : Tendsto
      (fun x : ℕ => Set.ncard (A ∩ Set.Icc 1 (2 * x)) - Set.ncard (A ∩ Set.Icc 1 x))
      atTop atTop)
    (hsum : ∀ θ : ℝ, 0 < θ → θ < 1 →
      ¬ Summable (fun n : ℕ => if n ∈ A then distNearestInt (θ * (n : ℝ)) else 0)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ S : Finset ℕ, ↑S ⊆ A ∧ ∑ x ∈ S, x = n := by
  sorry

end Erdos254
