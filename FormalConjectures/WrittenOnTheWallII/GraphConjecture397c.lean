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
# Written on the Wall II - Conjecture 397c

*References:*
- [E. DeLaVina, Written on the Wall II, entry 397c and definitions
  90/46/66/49/75](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, 2-domination and domination of the square: a constructive
  proof of Written on the Wall II 397c, 14 October 2026](https://github.com/google-deepmind/formal-conjectures/issues/7331)

Support vertices are the union of open neighborhoods of all leaves. The square
joins distinct vertices connected by one or two original edges. The linked
certificate proves the full universal statement and a set-transport theorem.
The excluded two-vertex complete graph really violates the inequality.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture397c

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def IsTwoDominating (D : Finset V) : Prop :=
  ∀ v ∉ D, 2 ≤ (D.filter fun w => G.Adj v w).card

noncomputable def twoDominationNumber : ℕ :=
  sInf {n | ∃ D : Finset V, IsTwoDominating G D ∧ D.card = n}

def supports : Finset V :=
  Finset.univ.filter fun s => ∃ p, G.degree p = 1 ∧ G.Adj p s

def square : SimpleGraph V where
  Adj v w := v ≠ w ∧ (G.Adj v w ∨ ∃ z, G.Adj v z ∧ G.Adj z w)
  symm := ⟨by
    intro v w h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | ⟨z,hz,hw⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨z,hw.symm,hz.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/--
WOWII 397c: every finite simple connected graph $G$ of order greater than two
satisfies $\gamma_2(G)\leq |V(G)\setminus N_G(P)|+\gamma(G^2)$, where $P$ is the
full leaf set and $N_G(P)$ is the union of its open neighborhoods. The square
uses original paths of length at most two. Only unselected vertices need two
selected neighbors. The linked proof covers every graph in the stated domain.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/66d81217cd33c8c37a3b1846289423ccff5c9ba4/Proofs/WOWII397cProof.lean"]
theorem conjecture397c : ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
      twoDominationNumber G ≤ (Finset.univ \ supports G).card + (square G).dominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture397c
