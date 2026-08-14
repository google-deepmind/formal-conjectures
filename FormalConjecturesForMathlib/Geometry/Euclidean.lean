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

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import FormalConjecturesForMathlib.Geometry.Metric

@[expose] public section

scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

/--
The minimal number of distinct distances determined by any set of $n$ points
in $\mathbb{R}^d$. This is the `d`-dimensional Euclidean analogue of
`Metric.minimalDistinctDistances`.
-/
noncomputable def Module.minimalDistinctDistances (d n : ℕ) : ℕ :=
  sInf {distinctDistances points |
    (points : Finset (EuclideanSpace ℝ (Fin d))) (_ : points.card = n)}
