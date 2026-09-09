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
# Written on the Wall II - Conjecture 144

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture144

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 144](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\mathrm{tree}(G) \ge \mathrm{girth}(G) - 1 + \mathrm{ecc}(\mathrm{Centers})$
where $\mathrm{tree}(G)$ is the largest induced tree size, $\mathrm{girth}(G)$ is
the length of the shortest cycle ($0$ if acyclic),
$\mathrm{Centers} = G.\mathrm{center}$ is the set of vertices with minimum
eccentricity (the center of $G$), and $\mathrm{ecc}(\mathrm{Centers})$ is the
eccentricity of the center set — the maximum distance from any non-center
vertex to the nearest center vertex.

**Proof sketch.** Let $g = \mathrm{girth}(G)$ and
$e = \mathrm{ecc}(G, \mathrm{center}(G))$. The acyclic and $e = 0$ cases are
immediate. If $g \le e + 2$, the formalized Bacsó--Tuza induced-path argument,
with an elementary $e = 1$ case, produces an induced tree on at least $2e + 1$
vertices. Since $g - 1 + e \le 2e + 1$, this proves the result.

Suppose instead that $e + 3 \le g$, and fix a shortest cycle $C$. Removing one
vertex of $C$ leaves an induced tree on $g - 1$ vertices. Analyze the connected
components outside $C$. If one has at least $e$ vertices, it supplies an
attached rooted induced tree of order $e$. Otherwise, let $D$ be the sum of the
components' attachment depths. If $D \ge e$, select pairwise edge-separated
rooted branches of total order $e$ and attach them to $C$, deleting a suitable
cycle vertex. If $D < e$, shortest-cycle contact restrictions bound
corresponding exclusion arcs. Their complement consists of central cycle
vertices and $D$-dominates the graph, forcing $e \le D$, a contradiction.

Finite graph search was used only during discovery to test candidate
structural lemmas and reject false proof templates; no finite-search result is
used in the universal proof.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/beowulf127/wowii144-lean/blob/046429d509b28c90ee2ec38ae27c1ad377c6a5fc/WOWII144/Main.lean"]
theorem conjecture144 (G : SimpleGraph α) (h : G.Connected) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by
  sorry

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The girth of any graph is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.girth := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture144
