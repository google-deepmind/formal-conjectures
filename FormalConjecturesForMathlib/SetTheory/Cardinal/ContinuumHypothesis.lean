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
`Cardinal.GCH` (Generalized Continuum Hypothesis) predicates, together with
basic API: the unfolding lemma `Cardinal.CH_iff`, the accessor
`Cardinal.GCH.aleph_succ`, the elementary implication `Cardinal.GCH.toCH`,
and the beth-aleph characterisation `Cardinal.GCH_iff_beth_eq_aleph`.

Mathlib has no built-in CH/GCH axiom; these are recorded here as `Prop`s to be
passed as hypotheses where needed in set-theoretic problems.

The formulation follows Jech/Kunen: `GCH` asserts that for every ordinal `o`,
`2 ^ ℵ_ o = ℵ_ (Order.succ o)`; equivalently, `ℶ_ o = ℵ_ o` for every `o`
(`Cardinal.GCH_iff_beth_eq_aleph`).
-/

namespace Cardinal

/-- The **Continuum Hypothesis**: $\mathfrak{c} = \aleph_1$. -/
def CH : Prop := (𝔠 : Cardinal.{0}) = ℵ_ 1

/-- The Continuum Hypothesis, unfolded to the power form $2^{\aleph_0} = \aleph_1$. -/
theorem CH_iff : CH ↔ (2 : Cardinal.{0}) ^ ℵ₀ = ℵ_ 1 := by
  rw [two_power_aleph0]
  exact Iff.rfl

/-- The **Generalized Continuum Hypothesis**: for every ordinal `o`,
$2^{\aleph_o} = \aleph_{o+1}$. -/
def GCH : Prop := ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ ℵ_ o = ℵ_ (Order.succ o)

/-- Accessor for `GCH` at a single ordinal, in the $\aleph_{o+1} = 2^{\aleph_o}$
orientation. -/
theorem GCH.aleph_succ (h : GCH) (o : Ordinal.{0}) :
    ℵ_ (Order.succ o) = (2 : Cardinal.{0}) ^ ℵ_ o :=
  (h o).symm

/-- GCH implies CH: apply GCH at `o = 0` and use `ℵ_ (Order.succ 0) = ℵ_ 1`. -/
theorem GCH.toCH (h : GCH) : CH := by
  unfold GCH at h
  unfold CH
  have h0 := h 0
  simpa [Cardinal.aleph_zero, Ordinal.succ_zero, two_power_aleph0] using h0

/-- The **beth-aleph characterisation of GCH**: `GCH` holds if and only if
$\beth_o = \aleph_o$ for every ordinal `o`. The forward direction is a transfinite
induction using `Cardinal.beth_succ` at successors and cofinality of the suprema at
limits; the backward direction rewrites $2^{\aleph_o} = 2^{\beth_o} = \beth_{o+1} =
\aleph_{o+1}$. -/
theorem GCH_iff_beth_eq_aleph : GCH ↔ ∀ o : Ordinal.{0}, ℶ_ o = ℵ_ o := by
  constructor
  · intro h o
    induction o using Ordinal.limitRecOn with
    | zero => rw [beth_zero, aleph_zero]
    | succ o ih => rw [beth_succ, ih, h o]
    | limit o ho ih =>
      rw [beth_limit ho, aleph_limit ho]
      exact iSup_congr fun i => ih i i.2
  · intro h o
    rw [← h o, ← beth_succ, h (Order.succ o)]

end Cardinal
