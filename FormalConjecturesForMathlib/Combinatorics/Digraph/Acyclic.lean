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

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation

/-!
# Acyclic directed graphs
-/

@[expose] public section

namespace Digraph

variable {V : Type*}

/-- A digraph is acyclic if it has no directed cycle, i.e. no vertex reaches itself by a
directed walk of positive length. -/
def IsAcyclic (D : Digraph V) : Prop := ∀ v, ¬ Relation.TransGen D.Adj v v

/-- The digraph obtained from `D` by reversing the direction of the arc `a → b`. -/
def reverseArc (D : Digraph V) (a b : V) : Digraph V where
  Adj x y := (D.Adj x y ∧ ¬ (x = a ∧ y = b)) ∨ (x = b ∧ y = a)

end Digraph
