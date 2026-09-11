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

public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# Monochromatic sets and Property B for hypergraph-style colourings

This file provides the colouring infrastructure shared by Erdős Problems 602 and 603.

A **colouring** of a type `α` by a colour type `C` is a function `f : α → C`. A set `A ⊆ α`
is **monochromatic** under `f` if `f` is constant on `A`. A family `(A_i)_{i ∈ I}` of subsets
of `α` has **`C`-chromatic Property B** if there exists a colouring `f : α → C` such that no
`A_i` is monochromatic.

When `C = Fin 2`, this reduces to the classical Property B of Erdős–Hajnal (a 2-colouring
with no monochromatic member). The general `C`-valued formulation is the natural setting
for Erdős Problem 603, which asks for the smallest cardinal `#C` for which every admissible
family admits a non-monochromatic colouring.

## Main definitions

* `Combinatorics.IsMonochromatic f A`: the set `A` is monochromatic under `f`.
* `Combinatorics.HasChromaticPropertyB C I A`: the family `A : I → Set α` admits a
  colouring `f : α → C` with no monochromatic member.

## References

* Erdős Problem 602 ([erdosproblems.com/602](https://www.erdosproblems.com/602)) —
  the `C = Fin 2` case.
* Erdős Problem 603 ([erdosproblems.com/603](https://www.erdosproblems.com/603)) —
  the cardinal-valued version.
-/

namespace Combinatorics

/-- A set `A ⊆ α` is **monochromatic** under a colouring `f : α → C`
if all elements of `A` receive the same colour. -/
def IsMonochromatic {α C : Type*} (f : α → C) (A : Set α) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, f x = f y

/-- A family `(A_i)_{i ∈ I}` of subsets of `α` has **`C`-chromatic Property B** if there exists
a colouring `f : α → C` (using at most `#C` colours) such that no `A_i` is monochromatic.

When `C = Fin 2`, this reduces to the classical Property B (2-colouring) of Erdős–Hajnal. -/
def HasChromaticPropertyB {α : Type*} (C : Type*) (I : Type*) (A : I → Set α) : Prop :=
  ∃ f : α → C, ∀ i, ¬IsMonochromatic f (A i)

end Combinatorics
