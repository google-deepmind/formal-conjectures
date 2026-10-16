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
# Written on the Wall II — Conjecture 252

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, A counterexample to Written on the Wall II Conjecture 252](https://github.com/user-attachments/files/33372321/Gebendorfer_WOWII_252_Intake_2026-10-13.zip)

Isolated vertices are excluded so that total dominating sets exist.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture252
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
def frequency (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℕ :=
  (univ.filter fun v => G.degree v = d).card

def modalCandidates (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ℕ :=
  (range (Fintype.card V)).filter fun d =>
    ∀ e ∈ range (Fintype.card V), frequency G e ≤ frequency G d

noncomputable def modeMin (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf (modalCandidates G : Set ℕ)

/-- No cycle on four distinct vertices, including cycles with chords. -/
def C4Free (G : SimpleGraph V) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False

/-- Every finite simple connected graph without isolated vertices and without
four-cycles was conjectured to satisfy $\gamma_t(G)\ge\operatorname{mode}_{\min}(G)$.
Four-cycles are excluded as subgraphs, including cycles with chords.
The least modal degree is the smallest degree value with maximum frequency.
The linked thirty-vertex witness has modal degree seven and total domination
number six.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/c934035169f0af19b9f821c7a72d12d8107d9e7d/Proofs/WOWII252Proof.lean"]
theorem conjecture252 : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], G.Connected →
      (∀ v, ∃ w, G.Adj v w) → C4Free G →
      modeMin G ≤ G.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture252
