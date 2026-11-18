/-
Copyright 2025 The Formal Conjectures Authors.

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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Path
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

variable {X : Type*} [MetricSpace X]

namespace Metric

open Set

def isLengthSpace : Prop :=
    ∀ x y : X, ∀ ε : ℝ, 0 < ε → ∃ γ : Path x y,
        eVariationOn ↑γ (Icc 0 1) < ENNReal.ofReal (dist x y + ε)

def CATZeroComparison (p q x y : X) : Prop :=
    ∀ p' q' x' y' : EuclideanSpace ℝ (Fin 2),
        dist p x = dist p' x' → dist p y = dist p' y' →
        dist x y = dist x' y' → dist q x = dist q' x' → dist q y = dist q' y' →
        ∀ z' ∈ segment ℝ x' y', dist p q ≤ dist p' z' + dist z' q'

def isCATZero : Prop :=
    ∀ p q x y : X, CATZeroComparison p q x y


end Metric


namespace SimpleGraph

/-- A metric space satisfies `Γ`-comparison if every configuration indexed by the
vertices of `Γ` admits a model in a real Hilbert space in which edge distances
are no larger and nonedge distances are no smaller than in the original
configuration. See Lebedeva and Petrunin, *5-point CAT(0) spaces after Tetsu
Toyoda*, §6 (arXiv:2009.09522v4).


For finite `V`, it suffices to take `EuclideanSpace ℝ V` as the model space.
For the finite-dimensional reduction, see Ostrovskii, *Metric Embeddings:
Bilipschitz and Coarse Embeddings into Banach Spaces* (De Gruyter, 2013),
proof of Proposition 1.21. -/
def GraphComparison {V : Type*} [Fintype V] (Γ : SimpleGraph V) : Prop :=
    ∀ x : V → X, ∃ y : V → EuclideanSpace ℝ V,
        (∀ i j, Γ.Adj i j → dist (y i) (y j) ≤ dist (x i) (x j)) ∧ (∀ i j, ¬ Γ.Adj i j → dist (y i) (y j) ≥ dist (x i) (x j))

end SimpleGraph
