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
# Erdős Problem 715

*Reference:* [erdosproblems.com/715](https://www.erdosproblems.com/715)

Does every regular graph of degree $4$ contain a regular subgraph of degree $3$?
Is there any $r$ such that every regular graph of degree $r$ must contain a regular
subgraph of degree $3$?

A problem of Berge (or Berge and Sauer). Alon, Friedland, and Kalai [AFK84]
proved that every $4$-regular graph plus an edge contains a $3$-regular subgraph,
and hence in particular every $r$-regular graph with $r \geq 5$ contains a $3$-regular
subgraph.

The answer is yes, proved by Tashkinov [Ta82].

[Er75] Erdős, P. (1975).

[Er81] Erdős, P. (1981).

[Ta82] Tashkinov, V. A., _Regular subgraphs of regular graphs_ (1982).

[AFK84] Alon, N., Friedland, S., and Kalai, G., _Regular subgraphs of almost
regular graphs_ (1984).
-/

open Classical SimpleGraph

namespace Erdos715

/--
**Erdős Problem 715** [Er75][Er81]:

Every $4$-regular simple graph contains a $3$-regular subgraph.

A subgraph $H$ of $G$ is $3$-regular if every vertex of $H$ has exactly $3$ neighbours
in $H$. We express this using Mathlib's `SimpleGraph.Subgraph`: there exists a
subgraph $H$ of $G$ such that `H.coe` (the coercion to a `SimpleGraph` on `H.verts`)
is $3$-regular, and $H$ has at least one vertex.

Proved by Tashkinov [Ta82].
-/
@[category research solved, AMS 5]
theorem erdos_715 : answer(True) ↔
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree 4 →
      ∃ H : G.Subgraph,
        H.verts.Nonempty ∧
        ∀ v : H.verts, H.degree v = 3 := by
  sorry

/--
**Erdős Problem 715, Variant** [AFK84]:

Every $r$-regular simple graph with $r \geq 5$ contains a $3$-regular subgraph.

Proved by Alon, Friedland, and Kalai [AFK84].
-/
@[category research solved, AMS 5]
theorem erdos_715.variants.r_geq_5 : answer(True) ↔
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (r : ℕ), r ≥ 5 →
      G.IsRegularOfDegree r →
      ∃ H : G.Subgraph,
        H.verts.Nonempty ∧
        ∀ v : H.verts, H.degree v = 3 := by
  sorry

end Erdos715
