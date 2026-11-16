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

public import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# Extremal parameters for hypergraphs

Shared counting and local-to-global parameters for uniform hypergraphs, designs, transversals
and dense subgraphs. Finite extrema use all labeled edge families; isomorphic copies are not
counted separately when counting edges or block-size profiles.
-/

namespace Hypergraph

open Filter

/-- All `r`-uniform hypergraphs on `n` vertices with exactly `m` edges. -/
def fixedSizeFamilies (n r m : ℕ) : Finset (Finset (Finset (Fin n))) :=
  ((Finset.univ : Finset (Fin n)).powersetCard r).powersetCard m

open scoped Classical in
/-- Probability of a matching in a uniformly chosen fixed-size edge family.
This is the cardinality of the event divided by that of the finite sample space; it is zero
when `m` exceeds the number of possible edges. -/
noncomputable def matchingProbability (n r m k : ℕ) : ℝ :=
  ((fixedSizeFamilies n r m).filter (fun H ↦ H.HasHypergraphMatching k)).card /
    ((fixedSizeFamilies n r m).card : ℝ)

open scoped Classical in
/-- Smallest independence number of a linear three-uniform hypergraph on `n` vertices. -/
noncomputable def linearIndependenceNumber (n : ℕ) : ℕ :=
  n - ((((Finset.univ : Finset (Fin n)).powersetCard 3).powerset.filter
    Finset.IsLinearHypergraph).sup fun H ↦ n - H.hypergraphIndependenceNumber)

/-- Maximum global transversal size under a local vertex-set constraint.
Infinity records that no finite bound works. -/
noncomputable def localTransversalBound (r v a : ℕ) : ℕ∞ :=
  ⨅ (b : ℕ) (_ : ∀ (n : ℕ) (H : Finset (Finset (Fin n))), H.IsUniform r →
    (∀ S : Finset (Fin n), S.card ≤ v →
      (H.hypergraphInduce S : Set (Finset (Fin n))).HasFiniteTransversal a) →
    (H : Set (Finset (Fin n))).HasFiniteTransversal b), (b : ℕ∞)

/-- Global transversal bound for a uniform family whose small subfamilies have small
transversals. Subfamilies with fewer than `q` edges are included. -/
noncomputable def subfamilyTransversalBound (k q a : ℕ) : ℕ∞ :=
  ⨅ (b : ℕ) (_ : ∀ (V : Type) (F : Set (Finset V)),
    (∀ e ∈ F, e.card = k) →
    (∀ E : Finset (Finset V), (↑E : Set _) ⊆ F → E.card ≤ q →
      (E : Set (Finset V)).HasFiniteTransversal a) → F.HasFiniteTransversal b), (b : ℕ∞)

/-- Least number of edges in an intersecting `r`-uniform family with transversal size `r`.
Infinity records a missing witness. -/
noncomputable def minIntersectingEdges (r : ℕ) : ℕ∞ :=
  ⨅ (n : ℕ) (H : Finset (Finset (Fin n))) (_ : H.IsUniform r)
    (_ : (H : Set (Finset (Fin n))).Intersecting)
    (_ : (H : Set (Finset (Fin n))).HasFiniteTransversal r)
    (_ : ¬ (H : Set (Finset (Fin n))).HasFiniteTransversal (r - 1)), (H.card : ℕ∞)

/-- Least vertex count forcing the Brown--Erdős--Sós little-o conclusion.
Infinity records the absence of a finite threshold. -/
noncomputable def sparseConfigurationThreshold (r e : ℕ) : ℕ∞ :=
  ⨅ (v : ℕ) (_ : (fun n ↦ (configurationExtremalNumber n r v e : ℝ))
    =o[atTop] (fun n ↦ (n : ℝ) ^ 2)), (v : ℕ∞)

/-- Edge density normalized by the number of possible uniform edges. -/
noncomputable def edgeDensity {n : ℕ} (r : ℕ) (H : Finset (Finset (Fin n))) : ℝ :=
  (H.card : ℝ) / n.choose r

/-- A density increase on growing induced vertex sets for every growing host sequence.
The boolean chooses the strict or weak lower bound at the initial density. -/
def HasDensityJump (r : ℕ) (α β : ℝ) (strict : Bool) : Prop :=
  ∀ (v : ℕ → ℕ), Tendsto v atTop atTop →
    ∀ G : (n : ℕ) → Finset (Finset (Fin (v n))),
      (∀ n, (G n).IsUniform r) →
      (if strict then α < atTop.liminf (fun n ↦ edgeDensity r (G n))
        else α ≤ atTop.liminf (fun n ↦ edgeDensity r (G n))) →
      ∃ S : (n : ℕ) → Finset (Fin (v n)),
        Tendsto (fun n ↦ (S n).card) atTop atTop ∧
        β < atTop.liminf (fun n ↦ ((G n).hypergraphInduce (S n)).card /
          ((S n).card.choose r : ℝ))

open scoped Classical in
/-- The least size above which a coloring gives both colors a positive share of every
induced complete uniform hypergraph. Positivity at `α = 0` retains the Ramsey convention. -/
noncomputable def balancedColoringThreshold (n r : ℕ) (α : ℝ) : ℕ :=
  sInf {m | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool, let count := ((X.powersetCard r).filter (fun e ↦ c e = b)).card
    0 < count ∧ α * (X.card.choose r : ℝ) ≤ count}

end Hypergraph
