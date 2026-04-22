/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 601

**Verbatim statement (Erdős #601, status O):**
> For which limit ordinals $\alpha$ is it true that if $G$ is a graph with vertex set $\alpha$ then $G$ must have either an infinite path or independent set on a set of vertices with order type $\alpha$?

**Source:** https://www.erdosproblems.com/601

**Notes:** OPEN - $500


*References:*
 - [erdosproblems.com/601](https://www.erdosproblems.com/601)
 - [EHM70] Erdős, Paul; Hajnal, András; Milner, Eric C., On sets of almost disjoint subsets
   of a set. Acta Math. Acad. Sci. Hungar. (1968), 209-218.
 - [La90] Larson, Jean A., Martin's Axiom and ordinal graphs: large independent sets or infinite
   paths. European J. Combin. (1990), 117-124.

## Problem Statement

For which limit ordinals $\alpha$ is it true that if $G$ is a graph with vertex set $\alpha$
(the ordinal $\alpha$ viewed as a set) then $G$ must have either an infinite path or an
independent set whose vertices have order type $\alpha$?

## Known Results

- **Erdős–Hajnal–Milner [EHM70]**: The property holds for all limit ordinals
  $\alpha < \omega_1^{\omega+2}$.
- **Larson [La90]**: Assuming Martin's Axiom (MA), the property holds for all limit
  ordinals $\alpha < 2^{\aleph_0}$.
- Erdős offered **$250** for settling the case $\alpha = \omega_1^{\omega+2}$ and
  **$500** for the general question (for which limit ordinals the property holds).

## Status: OPEN ($500 prize)

## Formalization Choices

- The vertex set of the graph is `α.ToType` (the type corresponding to the ordinal `α`).
- An **infinite path** in `G` is an injective sequence `f : ℕ → α.ToType` such that
  consecutive terms are adjacent: `G.Adj (f n) (f (n + 1))` for all `n`. This avoids
  the finite-length restriction of `SimpleGraph.Walk`.
- An **independent set of order type `α`** is a set `s ⊆ α.ToType` such that `G.IsIndepSet s`
  (pairwise non-adjacent) and `typeLT s = α` (order type equals `α`).
- A **limit ordinal** is formalized as `Order.IsSuccLimit α` (neither zero nor a successor).
- Martin's Axiom (MA) is not currently formalized in Mathlib; we state Larson's result
  with MA as an explicit `Prop` hypothesis.

## Overview

`HasPathOrIndepSetOfType α` captures the property for a single ordinal `α`:
every graph on `α.ToType` has either an infinite path or an independent set of order type `α`.

The main open problem `erdos_601` asks to characterize exactly which limit ordinals `α`
have this property.
-/

open Cardinal Ordinal SimpleGraph

namespace Erdos601

universe u

/- ### Key definition -/

/--
`HasPathOrIndepSetOfType α` holds for an ordinal `α` if every simple graph on `α.ToType`
contains either:
1. an **infinite path**: an injective function `f : ℕ → α.ToType` with `G.Adj (f n) (f (n+1))`
   for all `n`, or
2. an **independent set of order type `α`**: a set `s ⊆ α.ToType` that is pairwise
   non-adjacent in `G` and whose order type (under the well-order inherited from `α`) equals `α`.

This is the central property studied in Erdős Problem 601.
-/
def HasPathOrIndepSetOfType (α : Ordinal.{u}) : Prop :=
  ∀ G : SimpleGraph α.ToType,
    -- Either there exists an infinite path in G ...
    (∃ f : ℕ → α.ToType, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1))) ∨
    -- ... or there exists an independent set of order type α
    (∃ s : Set α.ToType, G.IsIndepSet s ∧ typeLT s = α)

/- ### Main open problem -/

/--
**Erdős Problem 601** (OPEN, **$500 prize**):

For which limit ordinals `α` does `HasPathOrIndepSetOfType α` hold?

That is: for which limit ordinals `α` is it true that every graph with vertex set `α`
must contain either an infinite path or an independent set whose vertices have order type `α`?

Erdős offered $250 for the case `α = ω₁ ^ (ω + 2)` and **$500 for the general characterization**.

*Known partial results:*
- Erdős–Hajnal–Milner proved the property holds for all `α < ω₁ ^ (ω + 2)`
  (see `erdos_601.variants.erdos_hajnal_milner_1970`).
- Larson proved the property holds for all `α < 2 ^ ℵ₀` assuming Martin's Axiom
  (see `erdos_601.variants.under_martin_axiom`).

**Status**: OPEN.
-/
@[category research open, AMS 5]
theorem erdos_601 :
    answer(sorry) ↔
    ∀ α : Ordinal.{0}, Order.IsSuccLimit α → HasPathOrIndepSetOfType α := by
  sorry

/- ### Variants and partial results -/

namespace erdos_601.variants

/--
**Erdős–Hajnal–Milner (1970)**: For all limit ordinals `α < ω₁^{ω+2}`,
every graph on `α.ToType` has either an infinite path or an independent set of order type `α`.

This is the known positive result up to (but not including) the threshold ordinal `ω₁^{ω+2}`.

**Status**: TRUE (Erdős–Hajnal–Milner).
-/
@[category research solved, AMS 5]
theorem erdos_hajnal_milner_1970 :
    ∀ α : Ordinal.{0},
      Order.IsSuccLimit α →
      α < ω_ 1 ^ (ω + 2) →
      HasPathOrIndepSetOfType α := by
  sorry

/--
**The $250 sub-question at `ω₁^{ω+2}`**: Does `HasPathOrIndepSetOfType (ω₁^{ω+2})` hold?

Erdős offered $250 specifically for determining whether every graph on `ω₁^{ω+2}`
has either an infinite path or an independent set of order type `ω₁^{ω+2}`.

The ordinal `ω₁^{ω+2}` is the first case not covered by the Erdős–Hajnal–Milner theorem.

**Status**: OPEN ($250 sub-prize).
-/
@[category research open, AMS 5]
theorem omega_1_omega_plus_2 :
    HasPathOrIndepSetOfType (ω_ 1 ^ (ω + 2)) := by
  sorry

/--
**Larson (1990), assuming Martin's Axiom**: For all limit ordinals `α < 2^{ℵ₀}`,
every graph on `α.ToType` has either an infinite path or an independent set of order type `α`.

Larson proved that under Martin's Axiom (MA), the property `HasPathOrIndepSetOfType α`
holds for all limit ordinals below the continuum `2^{ℵ₀}`.

Since Martin's Axiom is independent of ZFC and is not currently formalized in Mathlib,
we state it here as an explicit hypothesis `MA : Prop`. In a fuller formalization this
would be the appropriate axiom scheme from set theory.

**Status**: TRUE (under Martin's Axiom, Larson 1990).
-/
@[category research solved, AMS 5]
theorem under_martin_axiom
    -- Martin's Axiom, stated as an abstract hypothesis (not yet in Mathlib).
    (MA : Prop) :
    MA →
    ∀ α : Ordinal.{0},
      Order.IsSuccLimit α →
      α < Cardinal.continuum.ord →
      HasPathOrIndepSetOfType α := by
  sorry

/--
**Base case `α = ω`**: `HasPathOrIndepSetOfType ω` holds.

Every countably infinite graph on vertex set `ω` either contains an infinite path or has
an infinite independent set (and an infinite set has order type `ω`). This special case
follows from Ramsey-theoretic arguments (e.g., Ramsey's theorem for countable graphs
or König's infinity lemma) and also from the Erdős–Hajnal–Milner result since `ω < ω₁^{ω+2}`.

**Status**: TRUE.
-/
@[category research solved, AMS 5]
theorem at_omega : HasPathOrIndepSetOfType ω := by
  sorry

end erdos_601.variants

end Erdos601
