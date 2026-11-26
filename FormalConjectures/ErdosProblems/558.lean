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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 558

*References:*
- [erdosproblems.com/558](https://www.erdosproblems.com/558)
- [Er81c] Erdős, P., Some new problems and results in graph theory and other branches of
  combinatorial mathematics. Combinatorics and graph theory (1981), 9-17.
-/

@[expose] public section

namespace Erdos558

open SimpleGraph

/--
Let $R_k(G)$ denote the minimal $m$ such that if the edges of $K_m$ are $k$-coloured then there
is a monochromatic copy of $G$. Determine
$$R_k(K_{s,t})$$
where $K_{s,t}$ is the complete bipartite graph with $s$ vertices in one component and $t$ in the
other.

The parameters $k,s,t$ are positive integers.
-/
@[category research open, AMS 5]
theorem erdos_558 :
    let R : ℕ → ℕ → ℕ → ℕ := answer(sorry)
    ∀ k ≥ 1, ∀ s ≥ 1, ∀ t ≥ 1,
      IsLeast {m : ℕ | ∀ C : TopEdgeLabeling (Fin m) (Fin k),
        ∃ i, completeBipartiteGraph (Fin s) (Fin t) ⊑ C.labelGraph i} (R k s t) := by
  sorry

end Erdos558
