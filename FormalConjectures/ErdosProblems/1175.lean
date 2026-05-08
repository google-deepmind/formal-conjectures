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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1175

**Verbatim statement (Erdős #1175, status O):**
> Let $\kappa$ be an uncountable cardinal. Must there exist a cardinal $\lambda$ such that every graph with chromatic number $\lambda$ contains a triangle-free subgraph with chromatic number $\kappa$?

**Source:** https://www.erdosproblems.com/1175

**Notes:** OPEN


*Reference:* [erdosproblems.com/1175](https://www.erdosproblems.com/1175)

## Problem statement

Let $\kappa$ be an uncountable cardinal. Must there exist a cardinal $\lambda$ such that every
graph with chromatic number $\lambda$ contains a triangle-free subgraph with chromatic number
$\kappa$?

## Status

Open in ZFC. Shelah proved that a negative answer is consistent when $\kappa = \lambda = \aleph_1$:
there is a model of ZFC containing a graph with chromatic number $\aleph_1$ which has no
triangle-free subgraph with chromatic number $\aleph_1$.

## Formalization notes

- **Chromatic cardinal**: `SimpleGraph.chromaticCardinal` is the cardinal-valued chromatic number
  defined in `FormalConjecturesForMathlib`. It extends the finite `chromaticNumber` (which takes
  values in `ℕ∞`) to a `Cardinal`, and is therefore able to distinguish between different infinite
  chromatic numbers.
- **Triangle-free subgraph**: a subgraph `H : G.Subgraph` is triangle-free when `H.coe.CliqueFree 3`.
  This is the standard Mathlib formulation: `CliqueFree 3` means the graph has no `K₃` as a clique.
- **Subgraph**: we use `G.Subgraph` (a spanning subgraph record) rather than an induced subgraph
  since the problem asks for any subgraph, not just induced ones.
-/

open Cardinal SimpleGraph

namespace Erdos1175

/--
Let $\kappa$ be an uncountable cardinal. Must there exist a cardinal $\lambda$ such that every
graph with chromatic number $\lambda$ contains a triangle-free subgraph with chromatic number
$\kappa$?

This is an open problem of Erdős. Shelah proved that the answer can be **no** when
$\kappa = \lambda = \aleph_1$ (the consistency of a negative answer; see
`erdos_1175.variants.shelah_consistency`).

**Note on the answer**: The problem is open in ZFC. Shelah's result shows that a positive answer
is not provable from ZFC alone (since it fails in some model). Whether a negative answer is
consistent for all uncountable $\kappa$ is not known.
-/
@[category research open, AMS 5]
theorem erdos_1175 : answer(sorry) ↔
    ∀ (κ : Cardinal), ℵ₀ < κ →
      ∃ (μ : Cardinal),
        ∀ (V : Type*) (G : SimpleGraph V), G.chromaticCardinal = μ →
          ∃ (H : G.Subgraph), H.coe.CliqueFree 3 ∧ H.coe.chromaticCardinal = κ := by
  sorry

/--
**Shelah's consistency result**: it is consistent with ZFC that there exists a graph $G$ with
chromatic number $\aleph_1$ such that every triangle-free subgraph of $G$ has chromatic number
strictly less than $\aleph_1$.

This shows that a negative answer to Problem 1175 (with $\kappa = \lambda = \aleph_1$) is
consistent, so the main statement `erdos_1175` is not provable in ZFC.

**Formalization caveat (consistency placeholder).** Shelah's result is a *consistency*
statement — it asserts the existence of a model of ZFC, not a ZFC theorem. Lean operates
inside a single (fixed) model of its set theory, so we cannot directly express "consistent
with ZFC" without leaving ZFC. Rather than pretend that Shelah's theorem is a bare ZFC
negation, we record it here as an explicit `answer(sorry)` consistency placeholder: the
intended conjecture is the model-theoretic statement, and any concrete formalisation must
either appeal to an explicit extra axiom (such as Shelah's specific forcing extension)
or to a meta-theoretic consistency proof. Until such a wrapper exists in `FormalConjectures`,
we leave the body as `sorry`.
-/
@[category research solved, AMS 5]
theorem erdos_1175.variants.shelah_consistency : answer(sorry) ↔
    ¬ (∀ (V : Type*) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
         ∃ (H : G.Subgraph), H.coe.CliqueFree 3 ∧ H.coe.chromaticCardinal = ℵ_ 1) := by
  sorry

/--
**Equivalent reformulation**: the question can be phrased symmetrically as asking whether
uncountable chromatic number is "witnessed" by triangle-free subgraphs. Specifically,
for an uncountable $\kappa$, is there a universal threshold $\lambda$ such that any graph
of chromatic number $\geq \lambda$ has a triangle-free subgraph of chromatic number $\geq \kappa$?

This is equivalent to the original formulation when "chromatic number $= \lambda$" is
replaced by "chromatic number $\geq \lambda$", since we may always take $\lambda$ as the
minimum. We state it here as a variant for reference.
-/
@[category research open, AMS 5]
theorem erdos_1175.variants.threshold_formulation : answer(sorry) ↔
    ∀ (κ : Cardinal), ℵ₀ < κ →
      ∃ (μ : Cardinal),
        ∀ (V : Type*) (G : SimpleGraph V), μ ≤ G.chromaticCardinal →
          ∃ (H : G.Subgraph), H.coe.CliqueFree 3 ∧ H.coe.chromaticCardinal = κ := by
  sorry

/- ## Sanity checks and examples

The following `example` declarations demonstrate that the hypotheses and conclusions of the main
theorem are non-vacuous. All goals are fully closed: no `sorry`. -/

/-- The uncountability hypothesis `ℵ₀ < κ` is non-vacuous: `ℵ₁` is an uncountable cardinal.
This shows the main theorem has a concrete non-trivial instance. -/
@[category test, AMS 5]
example : ℵ₀ < ℵ_ 1 := by
  rw [← Cardinal.aleph_zero, Cardinal.aleph_lt_aleph]
  exact zero_lt_one

/-- Every graph has a triangle-free subgraph: the bottom subgraph (with no edges and
empty vertex set) is always triangle-free (`CliqueFree 3`).

This shows the existential `∃ H : G.Subgraph, H.coe.CliqueFree 3 ∧ ...` is non-vacuous:
the ⊥ subgraph witnesses triangle-freeness (though the chromatic number condition is
what makes the main problem hard). -/
@[category test, AMS 5]
example (V : Type*) (G : SimpleGraph V) : ∃ H : G.Subgraph, H.coe.CliqueFree 3 :=
  ⟨⊥, by simp [SimpleGraph.cliqueFree_bot (by norm_num : 2 ≤ 3)]⟩

/-- The edgeless graph on any type is triangle-free. This confirms `CliqueFree 3`
is a meaningful property: a graph with no edges has no triangles. -/
@[category test, AMS 5]
example (V : Type*) : (⊥ : SimpleGraph V).CliqueFree 3 :=
  SimpleGraph.cliqueFree_bot (by norm_num)

/-- The threshold formulation variant is stronger than the exact formulation:
if every graph with `chromaticCardinal ≥ μ` has the desired triangle-free subgraph,
then in particular every graph with `chromaticCardinal = μ` does too.
We verify this implication directly (at a fixed universe level, using `Type`). -/
@[category test, AMS 5]
theorem erdos_1175.threshold_implies_exact :
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
