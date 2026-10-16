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
# Cox–Duffy's oriented chromatic polynomial conjecture

*References:*
- [D. Cox, C. Duffy, Chromatic Polynomials of Oriented Graphs, Conjecture 12 (2019)](https://doi.org/10.37236/8240)
- [arXiv version, Conjecture 2.8](https://arxiv.org/pdf/1810.05590)
- [J. J. Gebendorfer, A Minimal Counterexample to Cox–Duffy Conjecture 12, 1 September 2026; manuscript archive](https://github.com/user-attachments/files/33368300/Cox_Intake_Gebendorfer_2026-10-13.zip)

The domain is purely oriented graphs. The earlier mixed-graph counterexample and
universal-vertex propagation idea are credited to Cox and Duffy. This does not
concern the distinct homomorphic polynomial of Das–Ghosh–Prabhu–Sen. Polynomial
identity is expressed by equality of counting values at every positive integer.

The obstruction convention here follows the published definition on p. 5:
condition (3) excludes undirected edges in `E_G`, not arcs in `A_G`. In this
purely oriented domain `E_G` is empty, so only the two-dipath exclusions remain.
In particular, a cross-pair joined by an arc is allowed. The archived manuscript
uses the adjacency-excluding variant; its minimum-order-five claim applies only
to that variant. Its five-vertex witness works under both conventions.
-/

@[expose] public section
namespace CoxDuffy

variable {V : Type*}

def IsOriented (A : V → V → Bool) : Prop :=
  (∀ v, A v v = false) ∧ ∀ u v, A u v = true → A v u = false

def IsOrientedColoring (A : V → V → Bool) {k : ℕ} (c : V → Fin k) : Prop :=
  (∀ u v, A u v = true → c u ≠ c v) ∧
  ∀ u v x y, A u v = true → A x y = true → c u = c y → c v ≠ c x

/-- Endpoints of a directed two-edge path in either direction. -/
def IsTwoPathEndpointPair (A : V → V → Bool) (u v : V) : Prop :=
  (∃ w, A u w = true ∧ A w v = true) ∨
    ∃ w, A v w = true ∧ A w u = true

/-- Published obstructing pairs, specialized to the purely oriented domain.
Both cross-pairs must avoid directed two-edge paths. Cross-arcs are allowed:
condition (3) in the paper excludes only undirected edges, absent here. -/
def HasObstructingPair (A : V → V → Bool) : Prop :=
  ∃ u v x y, A u v = true ∧ A x y = true ∧
    List.Pairwise (· ≠ ·) [u, v, x, y] ∧
    ¬ IsTwoPathEndpointPair A u y ∧ ¬ IsTwoPathEndpointPair A v x

/-- A four-vertex oriented graph whose underlying graph is a path. -/
def crossArcExample (u v : Fin 4) : Bool :=
  (u == 0 && v == 1) || (u == 2 && v == 3) || (u == 0 && v == 3)

@[category test, AMS 5]
theorem crossArcExample_isOriented : IsOriented crossArcExample := by
  unfold IsOriented crossArcExample
  decide

/-- Cross-arcs do not exclude an obstructing pair in the published convention. -/
@[category test, AMS 5]
theorem crossArcExample_hasObstructingPair : HasObstructingPair crossArcExample := by
  unfold HasObstructingPair IsTwoPathEndpointPair crossArcExample
  refine ⟨0, 1, 2, 3, ?_⟩
  decide

noncomputable def orientedCount [Fintype V] (A : V → V → Bool) (k : ℕ) : ℕ :=
  Nat.card {c : V → Fin k // IsOrientedColoring A c}

noncomputable def chromaticCount [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card (G.Coloring (Fin k))

/-- Existence of a simple graph with the same chromatic polynomial does not
characterize absence of obstructing arc pairs in finite oriented graphs. The
five-vertex manuscript witness and a four-vertex oriented path both disprove
the characterization under the published obstruction convention. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/RhudeJJJJ/formal-conjectures/blob/33c92b48ffe4ef192e2125ecf17681a62735e699/Proofs/CoxDuffyProof.lean#L49"]
theorem conjecture12 : ¬ ∀ (n : ℕ) (A : Fin n → Fin n → Bool), IsOriented A →
    ((∃ (m : ℕ) (G : SimpleGraph (Fin m)),
      ∀ k : ℕ, 0 < k → orientedCount A k = chromaticCount G k) ↔
        ¬ HasObstructingPair A) := by
  sorry

end CoxDuffy
