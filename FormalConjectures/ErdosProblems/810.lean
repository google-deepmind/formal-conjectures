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
# Erdős Problem 810

*Reference:* [erdosproblems.com/810](https://www.erdosproblems.com/810)

A problem of Burr, Erdős, Graham, and Sós. Asks whether there exists ε > 0 such that, for all
sufficiently large n, some n-vertex graph with at least εn² edges admits an n-coloring of its edges
where every C₄ is rainbow.

See also Problem 809.

[Er91] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Matematiche (Catania) **47** (1992), no. 2, 231-240 (1993).
-/

namespace Erdos810

/-- A graph on $n$ vertices admits a rainbow $C_4$ coloring with $n$ colors if there
    exists an edge coloring using $n$ colors such that every 4-cycle in the
    graph has all 4 edges receiving distinct colors. -/
def AdmitsRainbowC4Coloring (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ col : Sym2 (Fin n) → Fin n,
    ∀ (a b c d : Fin n),
      [a, b, c, d].Nodup →
      G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      [col (Sym2.mk (a, b)), col (Sym2.mk (b, c)),
       col (Sym2.mk (c, d)), col (Sym2.mk (d, a))].Nodup

/--
**Erdős Problem 810**: Does there exist some $\varepsilon > 0$ such that, for all
sufficiently large $n$, there exists a graph $G$ on $n$ vertices with at least
$\varepsilon n^2$ many edges such that the edges can be coloured with $n$ colours so that
every $C_4$ receives 4 distinct colours?
-/
@[category research open, AMS 5]
theorem erdos_810 : answer(sorry) ↔
    ∃ ε : ℝ, 0 < ε ∧
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ G : SimpleGraph (Fin n),
        (G.edgeSet.ncard : ℝ) ≥ ε * (n : ℝ) ^ 2 ∧
        AdmitsRainbowC4Coloring n G := by
  sorry

end Erdos810
