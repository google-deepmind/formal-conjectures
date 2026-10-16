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
# Written on the Wall II - Conjecture 373

*References:*
- [E. DeLaVina, Written on the Wall II, Conjecture 373,
  18 February 2009](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Peripheral distance and total domination in trees:
  a counterexample to WOWII 373, 13 October 2026](https://github.com/user-attachments/files/33421512/Gebendorfer_New_Proofs_Intakes_2026-10-14.zip)

The linked Lean certificate verifies the explicit 150-vertex counterexample.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture373

open SimpleGraph

/-- Vertices of maximum eccentricity, using ambient graph distance. -/
noncomputable def periphery {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∀ w,
    Finset.univ.sup (fun x => G.dist w x) ≤ Finset.univ.sup (fun x => G.dist v x)

/-- Average distance from peripheral vertices over pairs with distinct endpoints. -/
noncomputable def positivePeripheralAverage {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℚ :=
  (∑ u ∈ periphery G, ∑ v : V, G.dist u v : ℕ) /
    (((periphery G).card * (Fintype.card V - 1) : ℕ) : ℚ)

/--
WOWII Conjecture 373 proposed that every finite simple tree of order greater
than two has total domination number at least two thirds of its positive
average distance from the periphery to all vertices. The periphery consists
of vertices of maximum eccentricity. Distances are measured in the whole tree;
the average excludes zero self-distances and has denominator $|B|(|V|-1)$.
Gebendorfer's tree has a total dominating set of order 12 and positive
peripheral average $29514/1639$, giving a proposed lower bound $12+8/1639$.
The rational formulation is equivalent to the printed real-valued inequality.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/b45f7e0f6a05c2a8a483ee9695cba9de04730a3a/Proofs/WOWII373Proof.lean"]
theorem conjecture373 : answer(False) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsTree → 2 < Fintype.card V →
        (2 / 3 : ℚ) * positivePeripheralAverage G ≤ G.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture373
