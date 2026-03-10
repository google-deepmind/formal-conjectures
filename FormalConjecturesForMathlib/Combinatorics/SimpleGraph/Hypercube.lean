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
import Mathlib.Combinatorics.SimpleGraph.Basic

open Finset symmDiff

namespace SimpleGraph

/--
The hypercube graph `Q(n)` has as vertices the subsets of `Fin n` (represented as `Finset (Fin n)`).
Two vertices are adjacent if and only if they differ by exactly one element, i.e., their symmetric
difference has cardinality one.

- [Hypercube graph](https://en.wikipedia.org/wiki/Hypercube_graph)
-/
def hypercubeGraph (n : ℕ) : SimpleGraph (Finset (Fin n)) :=
  fromRel fun a b => (a ∆ b).card = 1

scoped notation "Q(" n ")" => hypercubeGraph n

end SimpleGraph
