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
# Oda's conjecture

This file formalizes Oda's conjecture.
The statements follow the formulation in Conjecture 1.1 of Tu's paper.

## References

* Tadao Oda, "Problems on Minkowski sums of convex lattice polytopes",
  https://arxiv.org/abs/0812.1418.

* Binnan Tu, "Oda's conjecture for reflexive polytopes: some special cases",
  https://arxiv.org/abs/2511.04322, Conjecture 1.1.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Pointwise

namespace Oda

variable {n : ℕ}

def latticeEmbedding (z : Fin n → ℤ) : Fin n → ℝ :=
  fun i => (z i : ℝ)

def latticePoints (P : Set (Fin n → ℝ)) : Set (Fin n → ℤ) :=
  {z | latticeEmbedding z ∈ P}

def IsLatticePolytope (P : Set (Fin n → ℝ)) : Prop :=
  ∃ S : Finset (Fin n → ℤ), S.Nonempty ∧
    P = convexHull ℝ (latticeEmbedding '' (S : Set (Fin n → ℤ)))

/-- The segment joining two distinct points is an edge of the polytope. -/
def IsEdge (P : Set (Fin n → ℝ)) (v w : Fin n → ℝ) : Prop :=
  v ≠ w ∧ IsExtreme ℝ P (segment ℝ v w)

/--
A full-dimensional smooth lattice polytope is called smooth if at each vertex `v`,
the other endpoints of the incident edges are exactly `v + lengths i • b i`,
where `b` is an integer lattice basis and the`lengths i` are positive integers.
-/
def IsSmoothLatticePolytope (P : Set (Fin n → ℝ)) : Prop :=
  IsLatticePolytope P ∧
  (interior P).Nonempty ∧
  ∀ v ∈ Set.extremePoints ℝ P,
    ∃ b : Module.Basis (Fin n) ℤ (Fin n → ℤ),
      ∃ lengths : Fin n → ℕ,
        (∀ i, 0 < lengths i) ∧
        ∀ w : Fin n → ℝ,
          IsEdge P v w ↔
            ∃ i : Fin n,
              w = v + (lengths i : ℝ) • latticeEmbedding (b i)

/-- Sums of exactly `k` elements of a set of lattice points. -/
def kFoldSum (A : Set (Fin n → ℤ)) (k : ℕ) : Set (Fin n → ℤ) :=
  {z | ∃ f : Fin k → (Fin n → ℤ),
    (∀ i, f i ∈ A) ∧ (∑ i : Fin k, f i) = z}

/-- The integer decomposition property. -/
def HasIDP (P : Set (Fin n → ℝ)) : Prop :=
  ∀ k : ℕ, 0 < k →
    latticePoints ((k : ℝ) • P) = kFoldSum (latticePoints P) k

/--
Oda's conjecture, Conjecture 1.1(1): every smooth lattice polytope has the
integer decomposition property.
-/
@[category research open, AMS 52]
theorem oda_conjecture :
    ∀ (n : ℕ) (P : Set (Fin n → ℝ)),
      IsSmoothLatticePolytope P → HasIDP P := by
  sorry

end Oda
