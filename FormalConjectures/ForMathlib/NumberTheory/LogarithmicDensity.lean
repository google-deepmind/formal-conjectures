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
import FormalConjectures.Util.ProblemImports

/-!
# Logarithmic Density

This file defines the logarithmic density of a set of natural numbers.

## Main definitions

* `HasLogarithmicDensity`: A set `A` has logarithmic density `d` if the sequence
  $(1 / \log n) \cdot \sum_{k \in A, k \le n} (1/k)$ converges to `d`.
-/

open Filter Finset Real Nat Set
open scoped Topology
open Classical

/--
A set `A` has logarithmic density `d` if the sequence
$(1 / \log n) \cdot \sum_{k \in A, k \le n} (1/k)$ converges to `d`.
-/
def HasLogarithmicDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun n => (∑ k ∈ range (n + 1) with k ∈ A, (1 : ℝ) / k) / Real.log n) atTop (𝓝 d)
