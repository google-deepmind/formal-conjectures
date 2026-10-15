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
- [J. J. Gebendorfer, A Minimal Counterexample to Cox–Duffy Conjecture 12, 1 September 2026; written disproof and intake](https://github.com/google-deepmind/formal-conjectures/issues/7255)

The domain is purely oriented graphs. The earlier mixed-graph counterexample and
universal-vertex propagation idea are credited to Cox and Duffy. This does not
concern the distinct homomorphic polynomial of Das–Ghosh–Prabhu–Sen. Polynomial
identity is expressed by equality of counting values at every positive integer.
-/

@[expose] public section
namespace CoxDuffy

variable {V : Type*}

def IsOriented (A : V → V → Bool) : Prop :=
  (∀ v, A v v = false) ∧ ∀ u v, A u v = true → A v u = false

def IsOrientedColoring (A : V → V → Bool) {k : ℕ} (c : V → Fin k) : Prop :=
  (∀ u v, A u v = true → c u ≠ c v) ∧
  ∀ u v x y, A u v = true → A x y = true → c u = c y → c v ≠ c x

/-- Adjacent vertices or endpoints of a directed two-edge path in either direction. -/
def IsProtectedPair (A : V → V → Bool) (u v : V) : Prop :=
  A u v = true ∨ A v u = true ∨
    (∃ w, A u w = true ∧ A w v = true) ∨
    ∃ w, A v w = true ∧ A w u = true

/-- Nonincident arcs with both cross-pairs unprotected. -/
def HasObstructingPair (A : V → V → Bool) : Prop :=
  ∃ u v x y, A u v = true ∧ A x y = true ∧
    List.Pairwise (· ≠ ·) [u, v, x, y] ∧
    ¬ IsProtectedPair A u y ∧ ¬ IsProtectedPair A v x

noncomputable def orientedCount [Fintype V] (A : V → V → Bool) (k : ℕ) : ℕ :=
  Nat.card {c : V → Fin k // IsOrientedColoring A c}

noncomputable def chromaticCount [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card (G.Coloring (Fin k))

/-- Existence of a simple graph with the same chromatic polynomial does not
characterize absence of obstructing arc pairs in finite oriented graphs. The
written witness is a five-vertex oriented path; minimality is not claimed by
this formal statement. -/
@[category research solved, AMS 5]
theorem conjecture12 : ¬ ∀ (n : ℕ) (A : Fin n → Fin n → Bool), IsOriented A →
    ((∃ (m : ℕ) (G : SimpleGraph (Fin m)),
      ∀ k : ℕ, 0 < k → orientedCount A k = chromaticCount G k) ↔
        ¬ HasObstructingPair A) := by
  sorry

end CoxDuffy
