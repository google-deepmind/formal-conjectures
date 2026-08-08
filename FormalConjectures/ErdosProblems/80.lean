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
# Erdős Problem 80

*References:*
- [erdosproblems.com/80](https://www.erdosproblems.com/80)
- [erdosproblems.com/600](https://www.erdosproblems.com/600), stated in
  `FormalConjectures/ErdosProblems/600.lean`

600 asks the same question from the other side. `Erdos600.eFunction n r` is the least edge
count forcing some edge into `r` triangles; `f c n` here is the largest book forced once the
edge count is at least $cn^2$. So `r ≤ f c n` and `Erdos600.eFunction n r ≤ c * n^2` say the
same thing, and the two functions are inverse to each other in that sense. Both are built on
`SimpleGraph.trianglesContaining`, which 600 introduced.
-/

open Filter Finset SimpleGraph

open scoped Topology

namespace Erdos80

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]

/-- The size of the largest *book* in `G`: the greatest number of triangles sharing a single
edge. `Finset.sup` gives `0` on a graph with no edges, which is the right answer there. -/
noncomputable def bookNumber : ℕ :=
  G.edgeFinset.sup fun e => #(G.trianglesContaining e)

/-- Every edge of `G` lies in at least one triangle. -/
def EveryEdgeInTriangle : Prop :=
  ∀ e ∈ G.edgeFinset, (G.trianglesContaining e).Nonempty

/-- The graphs the problem quantifies over: `n` vertices, at least $cn^2$ edges, and every
edge in a triangle. -/
def Admissible (c : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  c * (n : ℝ) ^ 2 ≤ #G.edgeFinset ∧ EveryEdgeInTriangle G

open Classical in
/-- $f_c(n)$, the largest book size forced on every admissible graph, which is the least book
number among them.

`sInf` of the empty set is `0`, so `f c n = 0` also when no graph on `n` vertices has $cn^2$
edges at all. That is the honest reading: nothing is forced when nothing qualifies. -/
noncomputable def f (c : ℝ) (n : ℕ) : ℕ :=
  sInf {m | ∃ G : SimpleGraph (Fin n), Admissible c G ∧ bookNumber G = m}

/--
Let $c>0$ and let $f_c(n)$ be the maximal $m$ such that every graph $G$ with $n$ vertices and
at least $cn^2$ edges, where each edge is contained in at least one triangle, must contain a
book of size $m$, that is, an edge shared by at least $m$ different triangles. Estimate
$f_c(n)$. In particular, is it true that $f_c(n)>n^\epsilon$ for some $\epsilon>0$?
-/
@[category research open, AMS 5]
theorem erdos_80 :
    answer(sorry) ↔ ∀ c : ℝ, 0 < c → ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ε < f c n := by
  sorry

/--
The weaker question from the same problem: is $f_c(n) \gg \log n$?
-/
@[category research open, AMS 5]
theorem erdos_80.variants.log :
    answer(sorry) ↔ ∀ c : ℝ, 0 < c →
      (fun n : ℕ ↦ (f c n : ℝ)) ≫ (fun n : ℕ ↦ Real.log n) := by
  sorry

omit [DecidableEq α] in
/-- A book is counted by triangles, so `bookNumber` is `0` exactly when no edge lies in one. -/
@[category API, AMS 5]
theorem bookNumber_eq_zero_iff :
    bookNumber G = 0 ↔ ∀ e ∈ G.edgeFinset, G.trianglesContaining e = ∅ := by
  simp [bookNumber, Finset.card_eq_zero]

/-- On a graph with no edges there is no book. -/
@[category test, AMS 5]
theorem bookNumber_bot {n : ℕ} : bookNumber (⊥ : SimpleGraph (Fin n)) = 0 := by
  simp [bookNumber]

/-- `EveryEdgeInTriangle` holds vacuously on a graph with no edges, so the admissible set is
nonempty only through the edge count. -/
@[category API, AMS 5]
theorem everyEdgeInTriangle_bot {n : ℕ} :
    EveryEdgeInTriangle (⊥ : SimpleGraph (Fin n)) := by
  simp [EveryEdgeInTriangle]

end Erdos80
