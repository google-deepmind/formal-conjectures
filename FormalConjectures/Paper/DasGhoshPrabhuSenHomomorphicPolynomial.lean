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
# Das–Ghosh–Prabhu–Sen, Question 25

*References:*
- [S. Das, S. Ghosh, S. Prabhu and S. Sen, A Homomorphic Polynomial for Oriented Graphs, Question 25](https://doi.org/10.37236/10726)
- [J. J. Gebendorfer, A Four-Vertex Counterexample to Refinement by the Homomorphic Polynomial of an Oriented Graph, 1 September 2026](https://github.com/user-attachments/files/33355710/Jonas_J_Gebendorfer_Q25_counterexample_reproducible_2026-09-01.zip)

The polynomial invariants are represented extensionally by their counting
functions on every positive integer. Equality therefore requires agreement at
all positive color counts. Homomorphic counts retain the target tournament as
part of each counted object and require surjectivity onto its exact image.
Oriented-coloring counts count each color map once.
-/

@[expose] public section
namespace DasGhoshPrabhuSen
variable {V W : Type*}

/-- A Boolean arc relation for a loopless oriented graph. -/
def IsOriented (A : V → V → Bool) : Prop :=
  (∀ v, A v v = false) ∧ ∀ u v, A u v = true → A v u = false

/-- The oriented-coloring condition, including the ordered pair of arcs. -/
def IsOrientedColoring (A : V → V → Bool) {x : ℕ} (c : V → Fin x) : Prop :=
  (∀ u v, A u v = true → c u ≠ c v) ∧
    ∀ u v w z, A u v = true → A w z = true → c u = c z → c v ≠ c w

/-- A tournament on the exact image of the color map. Entries involving unused
labels, and diagonal entries, are false, giving a unique extension to all labels.
-/
def IsTournamentOnImage {x : ℕ} (c : V → Fin x) (T : Fin x → Fin x → Bool) : Prop :=
  (∀ i j, T i j = true → i ≠ j ∧ (∃ u, c u = i) ∧ ∃ v, c v = j) ∧
    ∀ i j, (∃ u, c u = i) → (∃ v, c v = j) → i ≠ j → T i j ≠ T j i

def IsHomomorphicPair (A : V → V → Bool) {x : ℕ}
    (c : V → Fin x) (T : Fin x → Fin x → Bool) : Prop :=
  IsTournamentOnImage c T ∧ ∀ u v, A u v = true → T (c u) (c v) = true

noncomputable def homomorphicCount (A : V → V → Bool) (x : ℕ) : ℕ :=
  Nat.card {p : (V → Fin x) × (Fin x → Fin x → Bool) // IsHomomorphicPair A p.1 p.2}

noncomputable def orientedColoringCount (A : V → V → Bool) (x : ℕ) : ℕ :=
  Nat.card {c : V → Fin x // IsOrientedColoring A c}

/-! Explicit four-vertex witnesses from the written counterexample.
These finite orientation checks are kernel-reducible; the global counting
identity needed for `question25` remains a separate proof obligation. -/
def witnessG (u v : Fin 4) : Bool :=
  (u == 0 && v == 1) || (u == 0 && v == 2) || (u == 1 && v == 2)

def witnessH (u v : Fin 4) : Bool :=
  (u == 0 && v == 1) || (u == 1 && v == 2) || (u == 0 && v == 3)

@[category test, AMS 5]
theorem witnessG_isOriented : IsOriented witnessG := by
  unfold IsOriented witnessG
  decide

@[category test, AMS 5]
theorem witnessH_isOriented : IsOriented witnessH := by
  unfold IsOriented witnessH
  decide

/-- Does equality of homomorphic polynomials imply equality of oriented
chromatic polynomials for finite oriented graphs? The answer is negative.
Both identities below range over every positive integer, representing full
polynomial identity. The witness in the linked note has four vertices.
-/
@[question, category research solved, AMS 5]
theorem question25 : ¬ ∀ (V W : Type) [Fintype V] [Fintype W]
    (A : V → V → Bool) (B : W → W → Bool), IsOriented A → IsOriented B →
      (∀ x : ℕ, 0 < x → homomorphicCount A x = homomorphicCount B x) →
        ∀ x : ℕ, 0 < x → orientedColoringCount A x = orientedColoringCount B x := by
  sorry

end DasGhoshPrabhuSen
