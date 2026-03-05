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
# Erdős Problem 640

*Reference:* [erdosproblems.com/640](https://www.erdosproblems.com/640)

A problem of Erdős and Hajnal.

[Er97d] Erdős, P., *Some of my favourite problems in various branches of combinatorics*,
Matematiche (Catania) 52 (1997), 53-97.
-/

open SimpleGraph

namespace Erdos640

/--
Erdős Problem 640 (Erdős-Hajnal) [Er97d, p.84]:

For every $k \geq 3$, does there exist $f(k)$ such that every graph with chromatic number
at least $f(k)$ contains an odd cycle whose vertices span an induced subgraph
with chromatic number at least $k$?

This is trivial when $k = 3$, since any non-bipartite graph contains an odd cycle,
and all odd cycles have chromatic number $3$.
-/
@[category research open, AMS 5]
theorem erdos_640 :
    answer(sorry) ↔
    ∀ k : ℕ, 3 ≤ k →
      ∃ f : ℕ,
        ∀ (V : Type*) (G : SimpleGraph V),
          (f : ℕ∞) ≤ G.chromaticNumber →
          ∃ (v : V) (p : G.Walk v v),
            p.IsCycle ∧ Odd p.length ∧
            (k : ℕ∞) ≤ (G.induce {w : V | w ∈ p.support}).chromaticNumber := by
  sorry

end Erdos640
