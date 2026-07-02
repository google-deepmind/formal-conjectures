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

public import Mathlib.Data.Finset.Sym
public import Mathlib.Topology.MetricSpace.Defs

@[expose] public section

open scoped Finset

variable {X : Type*} [MetricSpace X]

/-- The number of pairs of points of a finite set `s` in a metric space that are distance 1 apart.
-/
noncomputable def unitDistNum (s : Finset X) : ℕ := #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}

/-- A set `A` in a metric space has *pairwise distinct distances* if any two pairs of distinct
points of `A` realising the same distance are equal as unordered pairs: whenever
`x, y, z, w ∈ A` with `x ≠ y`, `z ≠ w` and `dist x y = dist z w`, then `{x, y} = {z, w}`. -/
def PairwiseDistinctDistances (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ∀ w ∈ A,
    x ≠ y → z ≠ w → dist x y = dist z w → (x = z ∧ y = w) ∨ (x = w ∧ y = z)
