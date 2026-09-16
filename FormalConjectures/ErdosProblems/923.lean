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
# Erdős Problem 923

*References:*
- [erdosproblems.com/923](https://www.erdosproblems.com/923)
- [Er69b] Erdős, P., *Problems and results in chromatic graph theory*. Proof Techniques in Graph Theory (1969), 27-35.
- [Ro77] Rödl, V., *On the chromatic number of subgraphs of a given graph*. Proc. Amer. Math. Soc. (1977), 370-371.
-/

namespace Erdos923

open SimpleGraph

/--
Is it true that, for every $k$, there is some $f(k)$ such that if $G$ has chromatic number
$\geq f(k)$ then $G$ contains a triangle-free subgraph with chromatic number $\geq k$?

This is true, as shown by Rödl [Ro77].
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos923.lean"]
theorem erdos_923 : answer(True) ↔ ∀ (V : Type*) (n : ℕ),
    ∃ k : ℕ, ∀ G : SimpleGraph V, k ≤ G.chromaticNumber →
    ∃ H ≤ G, n ≤ H.chromaticNumber ∧ H.CliqueFree 3 := by
  sorry

end Erdos923
