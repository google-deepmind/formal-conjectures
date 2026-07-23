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
# Erdős Problem 150

*References:*
- [erdosproblems.com/150](https://www.erdosproblems.com/150)
- [Br24] Bradač, D., *On a question of Erdős and Nešetřil about minimal cuts in a graph*.
  arXiv:2409.02974 (2024).
- [Er88] Erdős, P., *Problems and results in combinatorial analysis and graph theory*.
  Discrete Math. (1988), 81-92.
- [FKTV08] Fomin, Fedor V. and Kratsch, Dieter and Todinca, Ioan and Villanger, Yngve, *Exact
  algorithms for treewidth and minimum fill-in*. SIAM J. Comput. (2008), 1058-1079.
- [FoVi12] Fomin, Fedor V. and Villanger, Yngve, *Treewidth computation and extremal
  combinatorics*. Combinatorica (2012), 289-308.
- [GaMa18] Gaspers, Serge and Mackenzie, Simon, *On the number of minimal separators in graphs*.
  J. Graph Theory (2018), 653-659.
-/

open Filter

open scoped Topology

namespace Erdos150

/-- A *minimal cut* of a graph `G` is a minimal set `T` of vertices whose removal disconnects
`G`, that is, `G - T` fails to be preconnected while `G - S` is preconnected for every `S ⊂ T`. -/
def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

/-- The maximum number $c(n)$ of minimal cuts a graph on $n$ vertices can have. -/
noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

/--
A minimal cut of a graph is a minimal set of vertices whose removal disconnects the graph. Let
$c(n)$ be the maximum number of minimal cuts a graph on $n$ vertices can have.

Does $c(n)^{1/n}\to \alpha$ for some $\alpha <2$?

It is unclear in [Er88] whether Erdős knew that the limit existed, which follows from a simple
argument first given in the literature (to the best of my knowledge) by Bradač [Br24].

That $\alpha<2$ was proved by Fomin, Kratsch, Todinca, and Villanger [FKTV08], who proved
$\alpha \leq 1.7087$. This was independently studied by Bradač [Br24] (unaware of this earlier
work), who proved that $\alpha \leq 2^{H(1/3)}\approx 1.8899$, where $H(\cdot)$ is the binary
entropy function.
-/
@[category research solved, AMS 5]
theorem erdos_150 : answer(True) ↔
    ∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α) := by
  sorry

/--
Asked by Erdős and Nešetřil, who also ask whether $c(3m+2)=3^m$.

Note that the lower bound $1.4457\leq \alpha$ of Gaspers and Mackenzie [GaMa18] provides a
negative answer to the above question of Erdős and Nešetřil.
-/
@[category research solved, AMS 5]
theorem erdos_150.variants.erdos_nesetril :
    answer(False) ↔ ∀ m : ℕ, maxMinimalCuts (3 * m + 2) = 3 ^ m := by
  sorry

/--
Seymour observed that $c(3m+2)\geq 3^m$, as seen by the graph of $m$ independent paths of length
$4$ joining two vertices.
-/
@[category research solved, AMS 5]
theorem erdos_150.variants.seymour (m : ℕ) : 3 ^ m ≤ maxMinimalCuts (3 * m + 2) := by
  sorry

/--
The current best-known bonds on $\alpha$ are\[1.4457\leq \alpha \leq \frac{1+\sqrt{5}}{2}\approx
1.618.\]The lower bound is due to Gaspers and Mackenzie [GaMa18].
-/
@[category research solved, AMS 5]
theorem erdos_150.variants.lower_bound (α : ℝ)
    (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) :
    1.4457 ≤ α := by
  sorry

/--
The current best-known bonds on $\alpha$ are\[1.4457\leq \alpha \leq \frac{1+\sqrt{5}}{2}\approx
1.618.\]The upper bound is due to Fomin and Villanger [FoVi12] (with a simpler proof in [GaMa18]).
-/
@[category research solved, AMS 5]
theorem erdos_150.variants.upper_bound (α : ℝ)
    (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) :
    α ≤ (1 + Real.sqrt 5) / 2 := by
  sorry

end Erdos150
