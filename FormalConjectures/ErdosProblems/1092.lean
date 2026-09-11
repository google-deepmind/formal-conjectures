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

import FormalConjecturesUtil

/-!
# Erdős Problem 1092

*References:*
- [Erdős Problem 1092](https://www.erdosproblems.com/1092)
- [Ro82] V. Rödl, *On the chromatic number of subgraphs of a given graph*, Proc. Amer. Math. Soc. **85** (1982), 382–386
-/

namespace Erdos1092

open SimpleGraph
open Finset
open Asymptotics
open Filter

open scoped Classical in
/--
An edge-budget function $g$ is *admissible* for $r$ if every graph $G$ with the property that every
subgraph $H$ on $m$ vertices is the union of a graph with chromatic number $\leq r$ and a graph
with $\leq g(m)$ edges has chromatic number $\leq r+1$.

The quantification is over all finite graphs $G$ (of any size), not just graphs on a fixed vertex
set, and the condition on subgraphs is imposed at every size $m$ simultaneously.

The function $f_r$ of the source is "maximal" among admissible functions. Since a function that is
pointwise at most an admissible function is again admissible, $f_r(n) \gg n$ means that some
admissible function grows at least linearly.
-/
def IsAdmissible (r : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ H : Subgraph G,
      ∃ E : Finset (Sym2 H.verts),
        E ⊆ H.coe.edgeFinset ∧ E.card ≤ g (Fintype.card H.verts) ∧
        chromaticNumber (H.coe.deleteEdges E) ≤ (r : ℕ∞)) →
    chromaticNumber G ≤ (r + 1 : ℕ∞)

/-- Is it true that $f_2(n) \gg n$? Disproved by Rödl, who showed $f_r(n) = o(n)$ for all fixed
$r \geq 2$. A conjecture of Erdős, Hajnal, and Szemerédi.

This seems to be closely related to, but distinct from, [744](https://www.erdosproblems.com/744).

Tang notes in the comments that Rödl [Ro82] constructed, for any $\epsilon>0$ and $k$, a graph
with chromatic number $\geq k$ such that every graph on $m$ vertices is bipartite after deleting at
most $\epsilon m$ edges. -/
@[category research solved, AMS 5]
theorem f_asymptotic_2 : answer(False) ↔
    ∃ g : ℕ → ℕ, IsAdmissible 2 g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ)) := by
  sorry

/-- More generally, is $f_r(n)\gg_r n$ for every $r \geq 2$? Disproved by Rödl, who showed
$f_r(n) = o(n)$ for all fixed $r \geq 2$. -/
@[category research solved, AMS 5]
theorem f_asymptotic_general : answer(False) ↔
    ∀ r : ℕ, 2 ≤ r → ∃ g : ℕ → ℕ, IsAdmissible r g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ)) := by
  sorry

end Erdos1092
