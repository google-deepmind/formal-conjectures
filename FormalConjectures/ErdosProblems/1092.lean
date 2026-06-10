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
# Erdős Problem 1092

*References:*
- [Erdős Problem 1092](https://www.erdosproblems.com/1092)
- [Ro82] V. Rödl, *On the chromatic number of subgraphs of a given graph*, Proc. Amer. Math. Soc. **85** (1982), 382–386
-/

namespace Erdos1092

open Classical
open SimpleGraph
open Finset
open Asymptotics
open Filter

/--
Let $f_r(m)$ be maximal such that, if any graph $G$ has the property that every subgraph $H$ on $m$
vertices is the union of a graph with chromatic number $\leq r$ and a graph with $\leq f_r(m)$
edges, then $G$ has chromatic number $\leq r+1$.

The quantification is over all finite graphs $G$ (of any size), not just graphs on a fixed vertex
set.
-/
noncomputable def f (r m : ℕ) : ℕ :=
  sSup {k : ℕ |
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ H : Subgraph G, Fintype.card H.verts = m →
        ∃ E : Finset (Sym2 H.verts),
          E ⊆ H.coe.edgeFinset ∧ E.card ≤ k ∧
          chromaticNumber (H.coe.deleteEdges E) ≤ (r : ℕ∞)) →
      chromaticNumber G ≤ (r + 1 : ℕ∞)}

/-- Is it true that $f_2(n) \gg n$? Disproved by Rödl, who showed $f_r(n) = o(n)$ for all fixed
$r \geq 2$. A conjecture of Erdős, Hajnal, and Szemerédi.

This seems to be closely related to, but distinct from, [744](https://www.erdosproblems.com/744).

Tang notes in the comments that Rödl [Ro82] constructed, for any $\epsilon>0$ and $k$, a graph
with chromatic number $\geq k$ such that every graph on $m$ vertices is bipartite after deleting at
most $\epsilon m$ edges. -/
@[category research solved, AMS 5]
theorem f_asymptotic_2 : answer(False) ↔
    (fun (n : ℕ) => (n : ℝ)) =o[atTop] (fun (n : ℕ) => (f 2 n : ℝ)) := by
  sorry

/-- More generally, is $f_r(n)\gg_r n$? Disproved by Rödl, who showed $f_r(n) = o(n)$ for all
fixed $r \geq 2$. -/
@[category research solved, AMS 5]
theorem f_asymptotic_general :
    answer(False) ↔ ∀ r : ℕ, (fun n : ℕ => ((r : ℝ) * n)) =o[atTop] (fun n : ℕ => (f r n : ℝ)) := by
  sorry

end Erdos1092
