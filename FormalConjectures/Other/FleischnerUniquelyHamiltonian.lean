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
# Fleischner's conjecture on uniquely Hamiltonian graphs

*References:*
* [Open Problem Garden](http://www.openproblemgarden.org/op/4_connected_graphs_are_not_uniquely_hamiltonian)
* [Fl14] Fleischner, H. (2014). "Uniquely Hamiltonian graphs of minimum degree 4."
  *J. Graph Theory* 75, pp. 167--177.
-/

@[expose] public section

open SimpleGraph

namespace FleischnerUniquelyHamiltonian

/--
**Fleischner's conjecture.**

Every $4$-connected graph with a Hamilton cycle has a second Hamilton cycle. Equivalently, no
$4$-connected graph is uniquely Hamiltonian.

Two Hamilton cycles are different when their edge sets are different.
-/
@[category research open, AMS 5]
theorem fleischner_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsKConnected G 4 → ¬ G.IsUniquelyHamiltonian := by
  sorry

end FleischnerUniquelyHamiltonian
