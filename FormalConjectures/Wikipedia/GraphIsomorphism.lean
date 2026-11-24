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
# The graph isomorphism problem

The graph isomorphism problem asks whether two given finite simple graphs are isomorphic.
It is not known whether this problem can be solved in polynomial time.
It is in NP, but it is not known to be NP-complete.
Babai (2016) gave a quasi-polynomial time algorithm.

*References:*
- [Wikipedia: Graph isomorphism problem](https://en.wikipedia.org/wiki/Graph_isomorphism_problem)
- [Wikipedia: List of unsolved problems in computer science](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_computer_science)
- László Babai, *Graph isomorphism in quasipolynomial time*, STOC 2016.
  [arXiv:1512.03547](https://arxiv.org/abs/1512.03547)
-/

@[expose] public section

namespace GraphIsomorphism

open ComplexityTheory

open scoped Classical in
/-- The graph isomorphism problem as a function. An input is a number of vertices $n$ together
with two simple graphs on `Fin n`. The output is whether the two graphs are isomorphic. -/
noncomputable def graphIsomorphic (x : Σ n, SimpleGraph (Fin n) × SimpleGraph (Fin n)) : Bool :=
  decide (Nonempty (x.2.1 ≃g x.2.2))

/--
**The graph isomorphism problem**: Can it be decided in polynomial time whether two finite
simple graphs are isomorphic?

The input is encoded by `BitstringEncoding`: the number of vertices $n$ in binary, then each
graph as its finite set of vertices together with its finite set of edges.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Graph_isomorphism_problem) -/
@[category research open, question, AMS 5 68]
theorem isPolyTime_graphIsomorphic : IsPolyTime graphIsomorphic := by
  sorry

end GraphIsomorphism
