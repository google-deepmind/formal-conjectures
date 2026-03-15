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
# Erdős Problem 563

For every 0 ≤ α < 1/2, let F(n, α) be the smallest m such that some 2-colouring of Kₙ forces
every m-subset of vertices to contain more than α · C(m, 2) edges of each colour. The conjecture
asserts that F(n, α) ~ c_α · log n for some constant c_α > 0.

*Reference:* [erdosproblems.com/563](https://www.erdosproblems.com/563)

[Er90b] Erdős, P., _Problems and results on graphs and hypergraphs: similarities and
differences_. Mathematics of Ramsey theory, Algorithms Combin. 5 (1990), 12-28.
-/

open Finset Filter

open scoped Topology

namespace Erdos563

/-- The number of edges of a given colour within a subset $X$, where the colouring
is given by a symmetric function $c : \operatorname{Fin}(n) \to \operatorname{Fin}(n)
\to \operatorname{Bool}$. An edge $\{i, j\}$ (with $i < j$) has colour $c(i,j)$. -/
def edgesOfColorInSubset {n : ℕ} (c : Fin n → Fin n → Bool)
    (X : Finset (Fin n)) (color : Bool) : ℕ :=
  ((X ×ˢ X).filter (fun p => p.1 < p.2 ∧ c p.1 p.2 = color)).card

/-- $F(n, \alpha)$: the smallest $m$ such that there exists a 2-colouring of the edges
of $K_n$ such that every subset of vertices of size $\geq m$ contains more than
$\alpha \cdot \binom{|X|}{2}$ edges of each colour. -/
noncomputable def fErdos563 (n : ℕ) (α : ℝ) : ℕ :=
  sInf {m : ℕ | ∃ (c : Fin n → Fin n → Bool),
    (∀ i j, c i j = c j i) ∧
    ∀ X : Finset (Fin n), (X.card : ℝ) ≥ (m : ℝ) →
      ∀ color : Bool,
        (edgesOfColorInSubset c X color : ℝ) >
          α * ((X.card : ℝ) * ((X.card : ℝ) - 1) / 2)}

/--
Erdős Problem 563 [Er90b]:

For every $0 \leq \alpha < 1/2$, there exists a constant $c_\alpha > 0$ such that
$$F(n, \alpha) \sim c_\alpha \cdot \log n,$$
i.e., $F(n, \alpha) / \log(n) \to c_\alpha$ as $n \to \infty$.
-/
@[category research open, AMS 5]
theorem erdos_563 (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1 / 2) :
    ∃ c : ℝ, c > 0 ∧
      Tendsto (fun n : ℕ => (fErdos563 n α : ℝ) / Real.log (n : ℝ))
        atTop (nhds c) := by
  sorry

end Erdos563
