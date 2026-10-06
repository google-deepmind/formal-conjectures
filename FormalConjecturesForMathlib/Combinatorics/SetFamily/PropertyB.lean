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


public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fin.Basic

@[expose] public section

/-!
# Property B

A family of sets has *property B* when the ground set admits a 2-colouring under which no member
of the family is monochromatic. For 3-uniform hypergraphs this is
`ThreeUniformHypergraph.IsTwoColorable`.
-/

namespace Finset

/-- A family `F` of finite sets has **property B** (equivalently, chromatic number `2`) if there
is a `2`-colouring of the ground set under which no member of `F` is monochromatic. -/
def HasPropertyB {α : Type*} (F : Finset (Finset α)) : Prop :=
  ∃ f : α → Fin 2, ∀ A ∈ F, ∃ x ∈ A, ∃ y ∈ A, f x ≠ f y

end Finset
