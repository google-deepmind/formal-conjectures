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
import Mathlib.Data.Finset.Sym
import Mathlib.Topology.MetricSpace.Defs

open scoped Finset

variable {X : Type*} [MetricSpace X]

/-- The number of pairs of points of a finite set `s` in a metric space that are distance 1 apart.
-/
noncomputable def unitDistNum (s : Finset X) : ℕ := #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}
