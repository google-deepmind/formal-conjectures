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
Let $f_r(n)$ be maximal such that, if a graph $G$ has the property that every subgraph $H$ on $m$
vertices is the union of a graph with chromatic number $\leq r$ and a graph with $\leq f_r(m)$
edges, then $G$ has chromatic number $\leq r+1$.

Erdős asked whether:
* `f 2 n ≫ n`
* more generally, `f r n ≫ r * n`

This was disproved by Rödl, who constructed, for any $\epsilon > 0$ and $k$, a graph with
chromatic number $\geq k$ such that every subgraph on $m$ vertices is bipartite after deleting at
most $\epsilon m$ edges. This proves (in a strong sense) that $f_r(n) = o(n)$ for all fixed
$r \geq 2$.

*References:*
- [Erdős Problem 1092](https://www.erdosproblems.com/1092)
- V. Rödl, *On the chromatic number of subgraphs of a given graph*,
  Proc. Amer. Math. Soc. **85** (1982), 382–386
-/

namespace Erdos1092

open Classical
open SimpleGraph
open Finset
open Asymptotics
open Filter

/--
$f_r(n)$ is maximal such that, if a graph $G$ on $n$ vertices has the property that every
subgraph $H$ on $m$ vertices has chromatic number $\leq r$ once we remove $f_r(m)$ edges
from it, then $G$ has chromatic number $\leq r+1$.
-/
noncomputable def f (r n : ℕ) : ℕ :=
  sSup {k : ℕ |
    ∀ G : SimpleGraph (Fin n),
      (∀ H : Subgraph G,
        ∃ E : Finset (Sym2 H.verts),
          E.card ≤ k ∧
          chromaticNumber (H.coe.deleteEdges E) ≤ (r : ℕ∞)) →
      chromaticNumber G ≤ (r + 1 : ℕ∞)}

/-- Is $f_2(n) \gg n$? Disproved by Rödl, who showed $f_r(n) = o(n)$ for all fixed $r \geq 2$. -/
@[category research solved, AMS 5]
theorem f_asymptotic_2 : answer(False) ↔
    (fun (n : ℕ) => (n : ℝ)) =o[atTop] (fun (n : ℕ) => (f 2 n : ℝ)) := by
  sorry

/-- Is $f_r(n) \gg_r n$ for all $r$? Disproved by Rödl, who showed $f_r(n) = o(n)$ for all fixed
$r \geq 2$. -/
@[category research solved, AMS 5]
theorem f_asymptotic_general :
    answer(False) ↔ ∀ r : ℕ, (fun n : ℕ => ((r : ℝ) * n)) =o[atTop] (fun n : ℕ => (f r n : ℝ)) := by
  sorry

end Erdos1092
