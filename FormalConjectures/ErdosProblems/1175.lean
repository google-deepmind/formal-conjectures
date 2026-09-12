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

import FormalConjecturesUtil

/-!
# Erdős Problem 1175

*Reference:* [erdosproblems.com/1175](https://www.erdosproblems.com/1175)

- [KoSh88] Komjáth, Péter and Shelah, Saharon, *Forcing constructions for uncountably chromatic
  graphs*. J. Symbolic Logic (1988), 696--707.

## Formalization notes

- **Chromatic cardinal**: `SimpleGraph.chromaticCardinal` is the cardinal-valued chromatic number
  defined in `FormalConjecturesForMathlib`. It extends the finite `chromaticNumber` (which takes
  values in `ℕ∞`) to a `Cardinal`, and is therefore able to distinguish between different infinite
  chromatic numbers.
- **Triangle-free subgraph**: a subgraph `H : G.Subgraph` is triangle-free when `H.coe.CliqueFree 3`.
  This is the standard Mathlib formulation: `CliqueFree 3` means the graph has no `K₃` as a clique.
- **Subgraph**: we use `G.Subgraph` (an arbitrary subgraph record) rather than an induced subgraph
  since the problem asks for any subgraph, not just induced ones.
-/

open Cardinal SimpleGraph

namespace Erdos1175

/--
Let $\kappa$ be an uncountable cardinal. Must there exist a cardinal $\lambda$ such that every
graph with chromatic number $\lambda$ contains a triangle-free subgraph with chromatic number
$\kappa$?

Shelah proved that a negative answer is consistent when
$\kappa = \lambda = \aleph_1$ (see `erdos_1175.variants.aleph_one`).
-/
@[category research open, AMS 5]
theorem erdos_1175 : answer(sorry) ↔
    ∀ (κ : Cardinal), ℵ₀ < κ →
      ∃ (μ : Cardinal),
        ∀ (V : Type*) (G : SimpleGraph V), G.chromaticCardinal = μ →
          ∃ (H : G.Subgraph), H.coe.CliqueFree 3 ∧ H.coe.chromaticCardinal = κ := by
  sorry

/--
The case $\kappa = \lambda = \aleph_1$ of Problem 1175: does every graph with chromatic number
$\aleph_1$ contain a triangle-free subgraph with chromatic number $\aleph_1$?

Shelah proved that a negative answer is consistent with ZFC [KoSh88, Theorem 1]: there is a
model of ZFC containing a graph with chromatic number $\aleph_1$ all of whose triangle-free
subgraphs have countable chromatic number. Consistency results about models of ZFC are not
directly formalizable inside Lean's fixed model, so only the underlying question is recorded
here. Note that this concerns only the choice $\lambda = \aleph_1$; it does not rule out a
larger $\lambda$ in `erdos_1175`.
-/
@[category research open, AMS 5]
theorem erdos_1175.variants.aleph_one : answer(sorry) ↔
    ∀ (V : Type*) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
      ∃ (H : G.Subgraph), H.coe.CliqueFree 3 ∧ H.coe.chromaticCardinal = ℵ_ 1 := by
  sorry

/--
**Threshold reformulation variant.** Replaces `chromaticCardinal = λ` in the hypothesis
of `erdos_1175` with `λ ≤ chromaticCardinal` (a graph of chromatic number ≥ λ has a
triangle-free subgraph of chromatic number κ). This is a strengthening of `erdos_1175`
(see `erdos_1175.test.threshold_implies_exact`).
-/
@[category research open, AMS 5]
theorem erdos_1175.variants.threshold_formulation : answer(sorry) ↔
    ∀ (κ : Cardinal), ℵ₀ < κ →
      ∃ (μ : Cardinal),
        ∀ (V : Type*) (G : SimpleGraph V), μ ≤ G.chromaticCardinal →
          ∃ (H : G.Subgraph), H.coe.CliqueFree 3 ∧ H.coe.chromaticCardinal = κ := by
  sorry

/- ## Sanity checks -/

/-- Every graph has a triangle-free subgraph: the bottom subgraph (with no edges)
witnesses triangle-freeness, so the existential
`∃ H : G.Subgraph, H.coe.CliqueFree 3` in `erdos_1175` is non-vacuous. -/
@[category test, AMS 5]
theorem erdos_1175.test.exists_triangle_free_subgraph
    (V : Type*) (G : SimpleGraph V) : ∃ H : G.Subgraph, H.coe.CliqueFree 3 :=
  ⟨⊥, by simp [SimpleGraph.cliqueFree_bot (by norm_num : 2 ≤ 3)]⟩

/-- The threshold variant `threshold_formulation` is stronger than the exact-equality
form `erdos_1175`: if every graph with `chromaticCardinal ≥ μ` has the desired
triangle-free subgraph, then in particular every graph with `chromaticCardinal = μ`
does too. -/
@[category test, AMS 5]
theorem erdos_1175.test.threshold_implies_exact :
    (∀ (κ : Cardinal.{0}), ℵ₀ < κ →
      ∃ (μ : Cardinal.{0}),
        ∀ (V : Type) (G : SimpleGraph V), μ ≤ G.chromaticCardinal →
          ∃ (H : G.Subgraph), H.coe.CliqueFree 3 ∧ H.coe.chromaticCardinal = κ) →
    (∀ (κ : Cardinal.{0}), ℵ₀ < κ →
      ∃ (μ : Cardinal.{0}),
        ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = μ →
          ∃ (H : G.Subgraph), H.coe.CliqueFree 3 ∧ H.coe.chromaticCardinal = κ) := by
  intro h κ hκ
  obtain ⟨μ, hμ⟩ := h κ hκ
  exact ⟨μ, fun V G hG => hμ V G hG.ge⟩

end Erdos1175
