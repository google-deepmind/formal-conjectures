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
# Written on the Wall II — Conjecture 361

*References:*
- [E. DeLaVina, Written on the Wall II, Conjecture 361, 18 February 2009](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, A Support–Center Lower Bound for Total Domination in Trees](https://github.com/user-attachments/files/33372731/Gebendorfer_WOWII_361_Intake_2026-10-13.zip)

The manuscript proves the source statement and extends it to the two-vertex
tree. Isolates are counted inside the induced support graph. The center consists
of vertices of minimum eccentricity, as defined by Mathlib.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture361
open SimpleGraph Finset

def supports {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∃ w, G.degree w = 1 ∧ G.Adj v w

def isolatedSupports {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  (supports G).filter fun v => ∀ w ∈ supports G, ¬ G.Adj v w

/-- Every finite simple tree of order greater than two satisfies
$\gamma_t(T)\ge iso(T[S(T)])+|C(T)|$, where $S(T)$ consists of neighbors
of leaves and $C(T)$ is the eccentricity/radius center.
-/
@[category research solved, AMS 5]
theorem conjecture361 {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (horder : 2 < Fintype.card V) :
    (isolatedSupports T).card + Nat.card T.center ≤ T.totalDominationNumber := by
  sorry

/-- The same inequality holds on all nontrivial finite simple trees, including
$K_2$, whose two support vertices are adjacent and are both centers.
-/
@[category research solved, AMS 5]
theorem conjecture361_nontrivial {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (horder : 1 < Fintype.card V) :
    (isolatedSupports T).card + Nat.card T.center ≤ T.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture361
