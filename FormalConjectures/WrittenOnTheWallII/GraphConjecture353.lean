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
# Written on the Wall II - Conjecture 353

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc,
  Conjecture 353, 18 February 2009](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, An infinite family of counterexamples to Written on
  the Wall II Conjecture 353, 13 October 2026](https://github.com/user-attachments/files/33421512/Gebendorfer_New_Proofs_Intakes_2026-10-14.zip)

The linked Lean certificate verifies the explicit 25-vertex counterexample.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture353

open SimpleGraph

/-- The largest component's vertex order, with value zero on the empty graph. -/
noncomputable def largestComponentOrder {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Finset.univ.sup fun v => Nat.card (G.connectedComponentMk v).supp

/--
WOWII Conjecture 353 proposed that every finite simple tree $T$ of order greater
than two satisfies
$$\gamma_t(T)\ge c(T[D_2])+\tfrac12 k_M,$$
where $D_2$ is the degree-two vertex set, $M$ the maximum-degree set, $c$ counts
connected components, and $k_M$ is the largest component order of $T[M]$.
Gebendorfer's 25-vertex tree has a total dominating set of order ten,
nine components on $D_2$, and a three-vertex component on $M$.
The rational comparison is equivalent to the printed real-valued inequality.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/c9f7e9b894fc0c979b57891f976c59f2b432273f/Proofs/WOWII353Proof.lean"]
theorem conjecture353 : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V →
      (Nat.card (G.induce {v | G.degree v = 2}).ConnectedComponent : ℚ) +
        (largestComponentOrder (G.induce {v | G.degree v = G.maxDegree}) : ℚ) / 2 ≤
          G.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture353
