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
# Written on the Wall II — Conjecture 253

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, A girth-five counterexample to Written on the Wall II Conjecture 253](https://github.com/user-attachments/files/33372380/Gebendorfer_WOWII_253_Intake_2026-10-13.zip)

Isolated vertices are excluded so that total dominating sets exist.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture253
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
def frequency (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℕ :=
  (univ.filter fun v => G.degree v = d).card

def modalCandidates (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ℕ :=
  (range (Fintype.card V)).filter fun d =>
    ∀ e ∈ range (Fintype.card V), frequency G e ≤ frequency G d

noncomputable def modeMin (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf (modalCandidates G : Set ℕ)

/-- Every finite simple connected graph without isolated vertices and with girth
at least five was conjectured to satisfy
$\gamma_t(G)\ge1+\operatorname{mode}_{\min}(G)$.
The least modal degree is the smallest degree value with maximum frequency.
Extended girth assigns infinity to forests. The linked thirty-vertex witness
has girth five, modal degree six and total domination number six.
The distinct catalogue result for girth at least seven is not refuted.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/c934035169f0af19b9f821c7a72d12d8107d9e7d/Proofs/WOWII253Proof.lean"]
theorem conjecture253 : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], G.Connected →
      (∀ v, ∃ w, G.Adj v w) → (5 : ℕ∞) ≤ G.egirth →
      1 + modeMin G ≤ G.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture253
