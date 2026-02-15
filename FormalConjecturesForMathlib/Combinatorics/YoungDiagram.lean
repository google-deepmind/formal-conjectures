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
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Combinatorics.SimpleGraph.Basic

open YoungDiagram

def YoungDiagram.Cell (μ : YoungDiagram) : Type := μ.cells

instance (μ : YoungDiagram) : Fintype μ.Cell :=
  inferInstanceAs (Fintype μ.cells)

instance (μ : YoungDiagram) : DecidableEq μ.Cell :=
  inferInstanceAs (DecidableEq μ.cells)

/-- The simple graph of a Young diagram: two distinct cells are
  adjacent iff they lie in the same row or in the same column. -/
def YoungDiagram.toSimpleGraph (μ : YoungDiagram) : SimpleGraph μ.Cell :=
  .fromRel fun a b => a.val.fst = b.val.fst ∨ a.val.snd = b.val.snd
