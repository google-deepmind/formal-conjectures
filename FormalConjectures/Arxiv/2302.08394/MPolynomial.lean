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
# Burghart's complete-invariant conjecture for the polynomial M

*References:*
- [F. Burghart, Polynomial invariants for rooted trees related to their random destruction, Definition 3 and Conjecture 20, version 3 (2024)](https://arxiv.org/html/2302.08394v3)
- [J. J. Gebendorfer, The Polynomial M Does Not Distinguish Rooted Trees, 31 August 2026; manuscript archive](https://github.com/user-attachments/files/33355697/Gebendorfer_M_counterexample_submission.zip)

The definitions below enumerate actual admissible vertex sets, boundary vertices,
and leaf subsets. They do not replace M by an assumed recurrence. Leaves have
no children in the rooting, not undirected degree one. The empty boundary
convention and division by X are explicit. Root-preserving isomorphism is required.
-/

@[expose] public section
namespace Burghart.MPolynomial
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def leaves (T : SimpleGraph V) (root : V) : Finset V := by
  classical
  exact univ.filter fun v => ¬ ∃ w, T.Adj v w ∧ T.dist root w = T.dist root v + 1

/-- Leaves in the descendant fringe rooted at v. -/
noncomputable def fringeLeaves (T : SimpleGraph V) (root v : V) : Finset V := by
  classical
  exact (leaves T root).filter fun l => T.dist root v + T.dist v l = T.dist root l

/-- Union of the actual v-to-leaf paths, empty for the empty leaf subset. -/
noncomputable def leafPathUnion (T : SimpleGraph V) (v : V) (A : Finset V) : Finset V := by
  classical
  exact univ.filter fun w => ∃ l ∈ A, T.dist v w + T.dist w l = T.dist v l

/-- p of a fringe tree, computed by 1-P(z,-1) from every leaf subset. -/
noncomputable def fringeP (T : SimpleGraph V) (root v : V) : Polynomial ℤ := by
  classical
  exact 1 - ∑ A ∈ (fringeLeaves T root v).powerset,
    Polynomial.C ((-1 : ℤ)^A.card) * Polynomial.X ^ (leafPathUnion T v A).card

def IsAdmissible (T : SimpleGraph V) (root : V) (S : Finset V) : Prop :=
  S = ∅ ∨ (root ∈ S ∧ (T.induce (S : Set V)).Connected ∧ Disjoint S (leaves T root))

noncomputable def boundary (T : SimpleGraph V) (root : V) (S : Finset V) : Finset V := by
  classical
  exact if S = ∅ then {root} else univ.filter fun v => v ∉ S ∧ ∃ u ∈ S, T.Adj u v

/-- Burghart's defining trivariate polynomial over integer coefficients.
Polynomial.divX divides each fringe p by z, as justified for trees by its zero
constant term; it does not introduce rational-function equality. -/
noncomputable def mPolynomial (T : SimpleGraph V) (root : V) : MvPolynomial (Fin 3) ℤ := by
  classical
  exact ∑ S ∈ univ.powerset.filter (IsAdmissible T root),
    MvPolynomial.X (0 : Fin 3) ^ S.card *
    MvPolynomial.X (1 : Fin 3) ^ ((boundary T root S).card - 1) *
    ∑ v ∈ boundary T root S,
      (fringeP T root v).divX.eval₂ (Int.castRingHom _) (MvPolynomial.X (2 : Fin 3))

/-- Equality of the M-polynomials does not imply root-preserving isomorphism
of finite rooted trees. The linked written witness has order 28; no universal
minimum-order claim is included here. -/
@[category research solved, AMS 5]
theorem conjecture20 : ¬ ∀ (n m : ℕ) (T : SimpleGraph (Fin n))
    (U : SimpleGraph (Fin m)) (r : Fin n) (s : Fin m), T.IsTree → U.IsTree →
      mPolynomial T r = mPolynomial U s → ∃ e : T ≃g U, e r = s := by
  sorry

end Burghart.MPolynomial
