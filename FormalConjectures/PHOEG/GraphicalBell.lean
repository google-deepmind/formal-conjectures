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
# Fixed-order, fixed-size graphical Bell conjecture

*References:*
- [PHOEG CSD8 presentation, displayed slides 29–31](https://orbi.umons.ac.be/bitstream/20.500.12907/7470/1/Hauweele_CSD8.pdf)
- [J. J. Gebendorfer, The Quasi-Complete Graph Minimizes Graphical Stirling Numbers at Fixed Order and Size, 25 July 2026](https://doi.org/10.5281/zenodo.21543038)
- [Statement intake and source comparison](https://github.com/google-deepmind/formal-conjectures/issues/7230)

Blocks are nonempty, independent and unlabeled. The stronger comparison is in
stable-partition counts, equivalently the falling-factorial chromatic basis;
it is not a comparison of ordinary monomial coefficients. Connectedness and
uniqueness of the extremal isomorphism type are not asserted.
-/

@[expose] public section
namespace PHOEG.GraphicalBell
open Finset SimpleGraph

/-- An actual partition into nonempty independent blocks, counted without labels. -/
def IsStablePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ B ∈ P, B.Nonempty ∧ G.IsIndepSet (B : Set V)) ∧
  (∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) ∧ P.biUnion id = univ

noncomputable def stirling {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card {P : Finset (Finset V) // IsStablePartition G P ∧ P.card = k}

noncomputable def bell {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  Nat.card {P : Finset (Finset V) // IsStablePartition G P}

def cliqueOrder (n m : ℕ) : ℕ := Nat.findGreatest (fun q => q.choose 2 ≤ m) n

/-- A clique, a vertex with the residual number of clique neighbors, and isolates.
At maximum feasible size the extra vertex is absent. -/
def quasiComplete (n m : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧
    ((u.val < cliqueOrder n m ∧ v.val < cliqueOrder n m) ∨
      (u.val = cliqueOrder n m ∧ v.val < m - (cliqueOrder n m).choose 2) ∨
      (v.val = cliqueOrder n m ∧ u.val < m - (cliqueOrder n m).choose 2))
  symm := ⟨by
    intro u v h
    constructor
    · exact Ne.symm h.1
    · rcases h.2 with h | h | h
      · exact Or.inl ⟨h.2, h.1⟩
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

/-- Every finite simple graph of order $n\ge1$ and size $m$ has at least as
many stable partitions as the quasi-complete graph $Q(n,m)$. -/
@[category research solved, AMS 5]
theorem conjecture {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 1 ≤ Fintype.card V) :
    bell (quasiComplete (Fintype.card V) G.edgeFinset.card) ≤ bell G := by
  sorry

/-- The written resolution strengthens the Bell bound coordinatewise for every
number of nonempty independent blocks. -/
@[category research solved, AMS 5]
theorem coefficientwise {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 1 ≤ Fintype.card V) (k : ℕ) :
    stirling (quasiComplete (Fintype.card V) G.edgeFinset.card) k ≤ stirling G k := by
  sorry

end PHOEG.GraphicalBell
