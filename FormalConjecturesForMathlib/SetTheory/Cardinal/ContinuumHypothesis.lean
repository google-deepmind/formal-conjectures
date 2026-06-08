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

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Continuum

@[expose] public section

/-!
# Continuum Hypothesis and Generalized Continuum Hypothesis

This file defines the `Cardinal.CH` (Continuum Hypothesis) and
`Cardinal.GCH` (Generalized Continuum Hypothesis) predicates,
together with the elementary implication `GCH → CH`.

Mathlib has no built-in CH/GCH axiom; these are recorded here as `Prop`s to be
passed as hypotheses where needed in set-theoretic problems.

The formulation follows Jech/Kunen: `GCH` asserts that for every ordinal `o`,
`2 ^ ℵ_ o = ℵ_ (Order.succ o)`. The equivalent beth-aleph formulation
(`ℶ_ o = ℵ_ o`) is recorded as `Cardinal.GCH_iff_beth_eq_aleph`.
-/

namespace Cardinal

/-- The **Continuum Hypothesis**: $2^{\aleph_0} = \aleph_1$. -/
def CH : Prop := (2 : Cardinal.{0}) ^ ℵ₀ = ℵ_ 1

/-- The **Generalized Continuum Hypothesis**: for every ordinal `o`,
$2^{\aleph_o} = \aleph_{o+1}$. -/
def GCH : Prop := ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ ℵ_ o = ℵ_ (Order.succ o)

/-- GCH implies CH: apply GCH at `o = 0` and use `ℵ_ (Order.succ 0) = ℵ_ 1`. -/
theorem GCH.toCH (h : GCH) : CH := by
  unfold GCH at h
  unfold CH
  have h0 := h 0
  simpa [Cardinal.aleph_zero, Ordinal.succ_zero] using h0

end Cardinal
