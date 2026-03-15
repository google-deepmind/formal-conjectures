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
# Erdős Problem 923

Is it true that, for every $k$, there is some $f(k)$ such that if $G$ has chromatic number
$\geq f(k)$ then $G$ contains a triangle-free subgraph with chromatic number $\geq k$?

*Reference:* [erdosproblems.com/923](https://www.erdosproblems.com/923)

[Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof Techniques in
Graph Theory (1969), 27–35.

[Ro77] Rödl, V., *On the chromatic number of subgraphs of a given graph*, Proc. Amer.
Math. Soc. 64 (1977), 370-371.
-/

open SimpleGraph

namespace Erdos923

/--
Is it true that, for every $k$, there is some $f(k)$ such that if $G$ has chromatic number
$\geq f(k)$ then $G$ contains a triangle-free subgraph with chromatic number $\geq k$?

Proved by Rödl [Ro77]. This is the $r = 4$ special case of problem \#108 [Er69b].
Triangle-free is formalized here as girth $\geq 4$ (no cycles of length 3).
-/
@[category research solved, AMS 5]
theorem erdos_923 :
    answer(True) ↔
      ∀ k ≥ (2 : ℕ),
        ∃ (f : ℕ),
          ∀ (V : Type*) (G : SimpleGraph V),
            (f : ℕ∞) ≤ G.chromaticNumber →
            ∃ H : G.Subgraph,
              (k : ℕ∞) ≤ H.coe.chromaticNumber ∧
              (4 : ℕ∞) ≤ H.coe.egirth := by
  sorry

end Erdos923
