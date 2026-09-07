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
# Erdős Problem 58

*References:*
- [erdosproblems.com/58](https://www.erdosproblems.com/58)
- [GaHuMa21] Gao, Jun and Huo, Qingyi and Ma, Jie, *A strengthening on odd cycles in graphs of given chromatic number*. SIAM J. Discrete Math. (2021), 2317-2327.
- [Gy92] Gyárfás, A., *Graphs with k odd cycle lengths*. Discrete Math. (1992), 41-48.
-/

namespace Erdos58

/--
If $G$ is a graph which contains odd cycles of $\leq k$ different lengths then $\chi(G)\leq 2k+2$,
with equality if and only if $G$ contains $K_{2k+2}$.

Conjectured by Bollobás and Erdős. Proved by Gyárfás [Gy92].
-/
@[category research solved, AMS 5]
theorem erdos_58 :
    ∀ {V : Type*} (G : SimpleGraph V) (k : ℕ),
      G.oddCycleLengths.ncard ≤ k →
        G.chromaticNumber ≤ (2 * k + 2 : ℕ∞) ∧
        (G.chromaticNumber = (2 * k + 2 : ℕ∞) ↔ (SimpleGraph.completeGraph (Fin (2 * k + 2))).IsContained G) := by
  sorry

end Erdos58
