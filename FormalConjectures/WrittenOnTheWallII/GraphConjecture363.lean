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
# Written on the Wall II — Conjecture 363

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Isolated supports and the periphery: A counterexample to Graffiti.pc Conjecture 363, 14 October 2026](https://github.com/google-deepmind/formal-conjectures/issues/7360)

This records the explicitly transcribed half-average version. Older archived
HTML can omit the multiplier. The linked certificate verifies a 27-vertex tree.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture363
open SimpleGraph

noncomputable def boundary {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∀ w,
    Finset.univ.sup (fun x => G.dist w x) ≤ Finset.univ.sup (fun x => G.dist v x)

noncomputable def distanceTo {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : Finset V) (v : V) : ℕ := by
  classical
  exact if h : B.Nonempty then B.inf' h (fun b => G.dist v b) else 0

noncomputable def positiveBoundaryAverage {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℚ :=
  (∑ v ∈ Finset.univ \ boundary G, distanceTo G (boundary G) v : ℕ) /
    (((Finset.univ \ boundary G).card : ℕ) : ℚ)

def supports {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => ∃ w, G.degree w = 1 ∧ G.Adj v w

def isolatedSupports {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  (supports G).filter fun v => ∀ w ∈ supports G, ¬ G.Adj v w

/-- For every finite simple tree of order greater than two, the proposed bound is
$\gamma_t(T)\ge i(T[S])+\tfrac12\operatorname{dist}_{\mathrm{avg}}(B,V)$,
where $S$ is the full support set and $B$ is the set of vertices of maximum
eccentricity. Here $i(T[S])$ counts isolated support vertices. The average is
of the minimum ambient distance to the set $B$ over vertices outside $B$.
The rational comparison is equivalent to the printed real-valued inequality.
The witness has six isolated supports, average $151/25$, and a total dominating
set of size nine, contradicting the proposed lower bound $451/50$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/603b96b621bbc34d366aa0091e8bc68e39a1e886/Proofs/WOWII363Proof.lean"]
theorem conjecture363 : answer(False) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V →
      ((isolatedSupports G).card : ℚ) + positiveBoundaryAverage G / 2 ≤
        G.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture363
