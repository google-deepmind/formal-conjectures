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
# Fleischner's conjecture: 4-connected graphs are not uniquely Hamiltonian
A graph is *uniquely Hamiltonian* if it contains exactly one Hamiltonian cycle
*References:*
- [Open Problem Garden](https://openproblemgarden.org/op/4_connected_graphs_are_not_uniquely_hamiltonian)
- H. Fleischner, *Uniquely Hamiltonian graphs of minimum degree 4*,
  J. Graph Theory 75 (2014), no. 2, 167–177, Section 3 (Concluding Remarks).
  [doi:10.1002/jgt.21729](https://doi.org/10.1002/jgt.21729)
-/

@[expose] public section

namespace Fleischner

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- **Fleischner's conjecture.**
Every 4-connected graph with a Hamiltonian cycle has a second Hamiltonian cycle, i.e. no 4-connected graph is uniquely Hamiltonian. -/
@[category research open, AMS 5]
theorem four_connected_not_uniquely_hamiltonian
  (h : G.IsKConnected 4) : ¬ G.IsUniquelyHamiltonian := by sorry

end Fleischner
