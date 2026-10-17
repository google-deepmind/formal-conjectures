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
# Written on the Wall II — Conjecture 376

*References:*
- [E. DeLaVina, Written on the Wall II, Conjecture 376, 18 February 2009](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Maximum-degree isolates and distance-sum minimizers: a proof of Graffiti.pc Conjecture 376, 13 October 2026](https://github.com/user-attachments/files/33421512/Gebendorfer_New_Proofs_Intakes_2026-10-14.zip)

The minimizing set below uses transmission, the sum of distances to all
vertices. It is distinct from the center defined by minimum eccentricity.
Isolates are counted in the graph induced by the ambient maximum-degree set.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture376
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, G.degree w ≤ G.degree v
def maximumDegreeIsolates (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  (maximumVertices G).filter fun v => ∀ w ∈ maximumVertices G, ¬ G.Adj v w

noncomputable def transmission (G : SimpleGraph V) (v : V) : ℕ := ∑ w : V, G.dist v w

noncomputable def medians (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∀ w, transmission G v ≤ transmission G w

/-- Every finite simple tree of order greater than two satisfies
$\gamma_t(T)\ge iso(T[M])+|Med(T)|$, where $M$ is its full ambient
maximum-degree set and $Med(T)$ consists of the vertices minimizing the sum
of distances to all vertices. Selected vertices also require a selected
neighbor in total domination.
-/
@[category research solved, AMS 5]
theorem conjecture376 (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 2 < Fintype.card V) :
    (maximumDegreeIsolates T).card + (medians T).card ≤ T.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture376
