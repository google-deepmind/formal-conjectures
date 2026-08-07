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

public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace SimpleGraph

/--
The number of edges of the complete graph on a finite vertex type `V` is `#V choose 2`.

This is a thin `completeGraph`-flavoured restatement of Mathlib's
`SimpleGraph.card_edgeFinset_top_eq_card_choose_two`, useful when a downstream definition
is stated using the `completeGraph V` abbreviation rather than the `⊤` form. (Because
`completeGraph V` reduces to `⊤`, the two are definitionally equal.)
-/
lemma card_edgeFinset_completeGraph (V : Type*) [Fintype V] [DecidableEq V] :
    ((completeGraph V).edgeFinset).card = (Fintype.card V).choose 2 :=
  card_edgeFinset_top_eq_card_choose_two

/-- Specialisation of `card_edgeFinset_completeGraph` to `Fin n`. -/
lemma card_edgeFinset_completeGraph_fin (n : ℕ) :
    ((completeGraph (Fin n)).edgeFinset).card = n.choose 2 := by
  simpa using card_edgeFinset_completeGraph (Fin n)

end SimpleGraph
