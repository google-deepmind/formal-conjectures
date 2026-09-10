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
# Erdős Problem 780

*References:*
- [erdosproblems.com/780](https://www.erdosproblems.com/780)
- [AFL86] Alon, N. and Frankl, P. and Lovász, L., The chromatic number of Kneser hypergraphs. Trans.
Amer. Math. Soc. (1986), 359-370.
- [Lo78] Lovász, L., Kneser's conjecture, chromatic number, and homotopy. J. Combin. Theory Ser. A
(1978), 319-324.
-/

namespace Erdos780

open Filter Asymptotics

/--
Suppose $n\geq kr+(t-1)(k-1)$ and the edges of the complete $r$-uniform hypergraph on $n$ vertices
are $t$-coloured. Prove that some colour class must contain $k$ pairwise disjoint edges.

The general case was proved by Alon, Frankl, and Lovász [AFL86].
-/
@[category research solved, AMS 5]
theorem erdos_780 :
    ∀ k r t n : ℕ, 1 ≤ k → 1 ≤ r → 1 ≤ t →
    k * r + (t - 1) * (k - 1) ≤ n → ∀ c : Finset (Fin n) → Fin t,
      ∃ M ⊆ (Finset.univ : Finset (Fin n)).powersetCard r,
        M.card = k ∧ (M : Set (Finset (Fin n))).Pairwise Disjoint ∧
          ∃ b : Fin t, ∀ e ∈ M, c e = b := by
  sorry

end Erdos780
