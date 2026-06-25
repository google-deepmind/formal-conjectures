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

*Reference:* [erdosproblems.com/923](https://www.erdosproblems.com/923)
-/

namespace Erdos923

open SimpleGraph

/--
For every $n$ there exists $f(n)$ such that any graph $G$ with $\chi(G) \ge f(n)$ has a
triangle-free subgraph $H$ with $\chi(H) \ge n$. This is a theorem of Rödl.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos923.lean"]
theorem erdos_923 {V : Type*} (n : ℕ) :
    ∃ k : ℕ, ∀ G : SimpleGraph V, k ≤ G.chromaticNumber →
    ∃ H ≤ G, n ≤ H.chromaticNumber ∧ H.CliqueFree 3 := by
  sorry

end Erdos923
