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
# Chen's Conjecture 4 on total domination and the delta-complement

*References:*
- [P. Chen, Refined Nordhaus–Gaddum-Type Bounds for Roman and Total Domination on delta-Complement Graphs, Mathematics 14 (2026), 1797, Conjecture 4](https://doi.org/10.3390/math14111797)
- [J. J. Gebendorfer, Total domination under complementation within a vertex partition, 14 October 2026](https://github.com/google-deepmind/formal-conjectures/issues/7335)

The degree partition is computed in the original graph. Delta-complementation
toggles edges within each original degree class and retains cross-class edges.
Only the absence of isolated vertices in both graphs is assumed; connectedness
is not required.
-/

@[expose] public section
namespace Chen.DeltaComplement
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def deltaComplement (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph V where
  Adj u v := (G.degree u = G.degree v ∧ u ≠ v ∧ ¬ G.Adj u v) ∨
    (G.degree u ≠ G.degree v ∧ G.Adj u v)
  symm := ⟨by
    intro u v h
    rcases h with ⟨hd, hn, ha⟩ | ⟨hd, ha⟩
    · exact Or.inl ⟨hd.symm, Ne.symm hn, fun hvu => ha hvu.symm⟩
    · exact Or.inr ⟨Ne.symm hd, ha.symm⟩⟩
  loopless := ⟨by
    intro v h
    rcases h with ⟨_, hn, _⟩ | ⟨hn, _⟩ <;> exact hn rfl⟩

def degreeClassCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (univ.image fun v => G.degree v).card

/-- If a finite simple graph $G$ and its delta-complement have no isolated
vertices, then $\gamma_t(G)+\gamma_t(G_\delta)\le n+2k$, where $k$ counts
the distinct degree values in the original $G$. No connectedness hypothesis
or condition on isolates within individual degree classes is imposed.
-/
@[category research solved, AMS 5]
theorem conjecture4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ v, ∃ w, G.Adj v w)
    (hDelta : ∀ v, ∃ w, (deltaComplement G).Adj v w) :
    G.totalDominationNumber + (deltaComplement G).totalDominationNumber ≤
      Fintype.card V + 2 * degreeClassCount G := by
  sorry

end Chen.DeltaComplement
