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
# Erdős Problem 1177

**Verbatim statement (Erdős #1177, status O):**
> Let $G$ be a finite $3$-uniform hypergraph, and let $F_G(\kappa)$ denote the collection of $3$-uniform hypergraphs with chromatic number $\kappa$ not containing $G$.If $F_G(\aleph_1)$ is not empty then there exists $X\in F_G(\aleph_1)$ of cardinality at most $2^{2^{\aleph_0}}$.If both $F_G(\aleph_1)$ and $F_H(\aleph_1)$ are non-empty then $F_G(\aleph_1)\cap F_H(\aleph_1)$ is non-empty.If $\kappa,\lambda$ are uncountable cardinals and $F_G(\kappa)$ is non-empty then $F_G(\lambda)$ is non-empty.

**Source:** https://www.erdosproblems.com/1177

**Notes:** OPEN


*Reference:* [erdosproblems.com/1177](https://www.erdosproblems.com/1177)

*References:*
- [EGH75] Erdős, Paul and Galvin, Fred and Hajnal, András, On set-systems having large
  chromatic number and not containing prescribed subsystems.
  Infinite and finite sets (Colloq., Keszthely, 1973; dedicated to P. Erdős on his 60th
  birthday), Vol. I. Colloq. Math. Soc. János Bolyai 10, North-Holland (1975), 425–513.

**Problem (Erdős, Galvin, Hajnal)**: Let $G$ be a finite 3-uniform hypergraph, and let
$\mathcal{F}_G(\kappa)$ denote the collection of 3-uniform hypergraphs with chromatic number
$\kappa$ not containing $G$ as a sub-hypergraph. Three conjectures:

1. If $\mathcal{F}_G(\aleph_1)$ is non-empty then there exists
   $X \in \mathcal{F}_G(\aleph_1)$ with $|X| \leq 2^{2^{\aleph_0}}$.

2. If both $\mathcal{F}_G(\aleph_1)$ and $\mathcal{F}_H(\aleph_1)$ are non-empty then
   $\mathcal{F}_G(\aleph_1) \cap \mathcal{F}_H(\aleph_1)$ is non-empty.

3. If $\kappa, \lambda$ are uncountable cardinals and $\mathcal{F}_G(\kappa)$ is non-empty
   then $\mathcal{F}_G(\lambda)$ is non-empty.

**Status:** OPEN (all three conjectures).

**Formalization notes:**
- A 3-uniform hypergraph on vertex type `V` is a pair `(edges, uniform)` where
  `edges : Set (Finset V)` and every edge has cardinality 3. This follows the same
  representation used in Problem 593 (`Erdos593.ThreeUniformHypergraph`).
- A proper coloring sends vertices to colors so that no hyperedge is monochromatic.
  The chromatic cardinal is the infimum of cardinalities of color types admitting a proper
  coloring.
- `FamilyAvoids G κ` is the set of pairs `⟨V, H⟩` (with `V : Type`) such that `H` has
  chromatic cardinal exactly `κ` and does not contain `G` as a sub-hypergraph.
  This formalizes $\mathcal{F}_G(\kappa)$.
- All `DecidableEq` instances are supplied automatically via `Classical` in this file.
-/

open Cardinal Set

namespace Erdos1177

open scoped Cardinal
open Classical

/- ## Definitions for 3-uniform hypergraphs

These definitions mirror those in Problem 593 (`Erdos593`); they are reproduced here so
that this file is self-contained. -/

/-- A **3-uniform hypergraph** on vertex type `V` is a set of 3-element `Finset`s.
Each element of `edges` is a hyperedge, and `uniform` ensures each has exactly 3 vertices.
This definition mirrors `Erdos593.ThreeUniformHypergraph`. -/
structure ThreeUniformHypergraph (V : Type) where
  /-- The set of hyperedges: each edge is a 3-element finset of vertices. -/
  edges : Set (Finset V)
  /-- Every hyperedge has exactly 3 vertices. -/
  uniform : ∀ e ∈ edges, e.card = 3

/-- A **proper coloring** of a 3-uniform hypergraph `H` by a color type `C` is a vertex
coloring such that no hyperedge is monochromatic (all three vertices receive the same color). -/
def ThreeUniformHypergraph.IsProperColoring {V : Type} (H : ThreeUniformHypergraph V)
    {C : Type} (f : V → C) : Prop :=
  ∀ e ∈ H.edges, ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- The **chromatic cardinal** of a 3-uniform hypergraph `H` is the infimum of cardinalities
of color types admitting a proper coloring. -/
noncomputable def ThreeUniformHypergraph.chromaticCardinal {V : Type}
    (H : ThreeUniformHypergraph V) : Cardinal.{0} :=
  sInf {κ : Cardinal.{0} | ∃ (C : Type), #C = κ ∧ ∃ f : V → C, H.IsProperColoring f}

/-- A 3-uniform hypergraph `F` **appears** in `H` (as a sub-hypergraph) if there exists an
injective vertex map `φ : W → V` that sends every hyperedge of `F` to a hyperedge of `H`.
We use `Classical.decEq` to provide `DecidableEq V` for `Finset.image`. -/
def ThreeUniformHypergraph.Appears {W V : Type} (F : ThreeUniformHypergraph W)
    (H : ThreeUniformHypergraph V) : Prop :=
  ∃ φ : W → V, Function.Injective φ ∧
    ∀ e ∈ F.edges, (e.image φ) ∈ H.edges

/- ## The family F_G(κ) -/

/-- `FamilyAvoids G κ` is the set of pairs `⟨V, H⟩` where `V : Type`,
`H : ThreeUniformHypergraph V`, `H.chromaticCardinal = κ`, and `G` does not appear in `H`.

This formalizes $\mathcal{F}_G(\kappa)$ from the problem statement. -/
def FamilyAvoids {W : Type} (G : ThreeUniformHypergraph W)
    (κ : Cardinal.{0}) : Set (Σ V : Type, ThreeUniformHypergraph V) :=
  {p | p.2.chromaticCardinal = κ ∧ ¬ G.Appears p.2}

/- ## Main conjectures -/

/--
**Erdős–Galvin–Hajnal Problem 1177, Conjecture 1**: If $\mathcal{F}_G(\aleph_1)$ is non-empty
then there exists $X \in \mathcal{F}_G(\aleph_1)$ of cardinality at most $2^{2^{\aleph_0}}$.

More precisely: if there exists a 3-uniform hypergraph with chromatic cardinal $\aleph_1$ not
containing $G$, then there is such a hypergraph whose vertex set has cardinality at most
$2^{2^{\aleph_0}}$.

*Original statement (erdosproblems.com/1177)*:
"If $\mathcal{F}_G(\aleph_1)$ is non-empty then there exists $X \in \mathcal{F}_G(\aleph_1)$
of cardinality at most $2^{2^{\aleph_0}}$."

**Status:** OPEN.
-/
@[category research open, AMS 5]
theorem erdos_1177.conjectures.one :
    answer(sorry) ↔
    ∀ {W : Type} [Fintype W] (G : ThreeUniformHypergraph W),
      (FamilyAvoids G (ℵ_ 1)).Nonempty →
      ∃ p ∈ FamilyAvoids G (ℵ_ 1), #p.1 ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ ℵ₀) := by
  sorry

/--
**Erdős–Galvin–Hajnal Problem 1177, Conjecture 2**: If both $\mathcal{F}_G(\aleph_1)$ and
$\mathcal{F}_H(\aleph_1)$ are non-empty then $\mathcal{F}_G(\aleph_1) \cap \mathcal{F}_H(\aleph_1)$
is non-empty.

More precisely: if there exist 3-uniform hypergraphs with chromatic cardinal $\aleph_1$ avoiding
$G$ and $H$ separately, then there is a single such hypergraph avoiding both simultaneously.

*Original statement (erdosproblems.com/1177)*:
"If both $\mathcal{F}_G(\aleph_1)$ and $\mathcal{F}_H(\aleph_1)$ are non-empty then
$\mathcal{F}_G(\aleph_1) \cap \mathcal{F}_H(\aleph_1)$ is non-empty."

**Status:** OPEN.
-/
@[category research open, AMS 5]
theorem erdos_1177.conjectures.two :
    answer(sorry) ↔
    ∀ {W₁ : Type} [Fintype W₁] (G : ThreeUniformHypergraph W₁)
      {W₂ : Type} [Fintype W₂] (H : ThreeUniformHypergraph W₂),
      (FamilyAvoids G (ℵ_ 1)).Nonempty →
      (FamilyAvoids H (ℵ_ 1)).Nonempty →
      ∃ V : Type, ∃ X : ThreeUniformHypergraph V,
        X.chromaticCardinal = ℵ_ 1 ∧ ¬ G.Appears X ∧ ¬ H.Appears X := by
  sorry

/--
**Erdős–Galvin–Hajnal Problem 1177, Conjecture 3**: If $\kappa, \mu$ are uncountable
cardinals and $\mathcal{F}_G(\kappa)$ is non-empty then $\mathcal{F}_G(\mu)$ is non-empty.

More precisely: the property "there exists a 3-uniform hypergraph with chromatic cardinal
$\kappa$ avoiding $G$" depends only on whether $\kappa$ is uncountable, not on the specific
uncountable cardinal chosen.

*Original statement (erdosproblems.com/1177)*:
"If $\kappa, \lambda$ are uncountable cardinals and $\mathcal{F}_G(\kappa)$ is non-empty then
$\mathcal{F}_G(\lambda)$ is non-empty."
(We use $\mu$ in place of $\lambda$ to avoid conflict with Lean 4's reserved `λ` keyword.)

**Status:** OPEN.
-/
@[category research open, AMS 5]
theorem erdos_1177.conjectures.three :
    answer(sorry) ↔
    ∀ {W : Type} [Fintype W] (G : ThreeUniformHypergraph W)
      (κ μ : Cardinal.{0}),
      ℵ₀ < κ → ℵ₀ < μ →
      (FamilyAvoids G κ).Nonempty →
      (FamilyAvoids G μ).Nonempty := by
  sorry

/--
**Erdős–Galvin–Hajnal Problem 1177 (combined statement)**: All three conjectures hold simultaneously.

This bundles the three individual open conjectures into a single statement.

*A problem of Erdős, Galvin, and Hajnal [EGH75].*

**Status:** OPEN.
-/
@[category research open, AMS 5]
theorem erdos_1177 : answer(sorry) ↔
    (∀ {W : Type} [Fintype W] (G : ThreeUniformHypergraph W),
      (FamilyAvoids G (ℵ_ 1)).Nonempty →
      ∃ p ∈ FamilyAvoids G (ℵ_ 1), #p.1 ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ ℵ₀)) ∧
    (∀ {W₁ : Type} [Fintype W₁] (G : ThreeUniformHypergraph W₁)
       {W₂ : Type} [Fintype W₂] (H : ThreeUniformHypergraph W₂),
      (FamilyAvoids G (ℵ_ 1)).Nonempty →
      (FamilyAvoids H (ℵ_ 1)).Nonempty →
      ∃ V : Type, ∃ X : ThreeUniformHypergraph V,
        X.chromaticCardinal = ℵ_ 1 ∧ ¬ G.Appears X ∧ ¬ H.Appears X) ∧
    (∀ {W : Type} [Fintype W] (G : ThreeUniformHypergraph W)
       (κ μ : Cardinal.{0}),
      ℵ₀ < κ → ℵ₀ < μ →
      (FamilyAvoids G κ).Nonempty →
      (FamilyAvoids G μ).Nonempty) := by
  sorry

/- ## Variants and sanity checks -/

/--
**The bound in Conjecture 1**: We verify $\aleph_1 \leq 2^{2^{\aleph_0}}$, confirming the
bound in Conjecture 1 is consistent with the chromatic cardinal $\aleph_1$.

The chain is: $\aleph_1 \leq 2^{\aleph_0}$ (by `aleph_one_le_continuum`) and
$2^{\aleph_0} \leq 2^{2^{\aleph_0}}$ (by `Cardinal.power_le_power_right` and `Cardinal.cantor`).
-/
@[category test, AMS 5]
example : ℵ_ 1 ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ ℵ₀) := by
  -- ℵ₁ ≤ 𝔠 = 2^ℵ₀ ≤ 2^(2^ℵ₀) (by monotonicity of exponentiation, Cantor gives ℵ₀ < 2^ℵ₀)
  calc ℵ_ 1 ≤ 𝔠 := aleph_one_le_continuum
    _ = (2 : Cardinal) ^ ℵ₀ := two_power_aleph0.symm
    _ ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ ℵ₀) :=
        Cardinal.power_le_power_left (by norm_num) (Cardinal.cantor ℵ₀).le

/--
**Concrete instances for Conjecture 3**: $\aleph_1$ and $\aleph_2$ are both uncountable,
so the pair $(\kappa, \mu) = (\aleph_1, \aleph_2)$ is a concrete non-trivial instance of
the hypothesis of Conjecture 3.
-/
@[category test, AMS 5]
example : ℵ₀ < ℵ_ 1 ∧ ℵ₀ < ℵ_ 2 := by
  constructor
  · rw [← Cardinal.aleph_zero]; exact Cardinal.aleph_lt_aleph.mpr zero_lt_one
  · rw [← Cardinal.aleph_zero]; exact Cardinal.aleph_lt_aleph.mpr (by norm_num)

/--
**Transitivity of `Appears`**: if `G₁` appears in `G₂` and `G₂` appears in `H`, then
`G₁` appears in `H`. This is the key composition property underlying Problem 593's
`obligatory_monotone` result.
-/
@[category textbook, AMS 5]
theorem erdos_1177.variants.appears_trans
    {W₁ W₂ V : Type}
    {G₁ : ThreeUniformHypergraph W₁} {G₂ : ThreeUniformHypergraph W₂}
    {H : ThreeUniformHypergraph V}
    (h12 : G₁.Appears G₂) (h2H : G₂.Appears H) :
    G₁.Appears H := by
  obtain ⟨φ, hφ_inj, hφ_edge⟩ := h12
  obtain ⟨ψ, hψ_inj, hψ_edge⟩ := h2H
  exact ⟨ψ ∘ φ, hψ_inj.comp hφ_inj,
    fun e he => by
      have himg := hψ_edge (e.image φ) (hφ_edge e he)
      rwa [Finset.image_image] at himg⟩

/--
**Monotonicity of `FamilyAvoids`**: if `G₂` appears in `G₁` (i.e., `G₂` embeds as a
sub-hypergraph into `G₁`) then `FamilyAvoids G₂ κ ⊆ FamilyAvoids G₁ κ`.

Intuition: if `X` avoids `G₂` (a pattern that contains `G₁` via `G₂.Appears G₁`), and
`G₁` were to appear in `X`, then by transitivity (`appears_trans`) `G₂` would appear in `X`,
contradicting the assumption. Hence avoiding the sub-pattern `G₂` is harder: fewer hypergraphs
are in `FamilyAvoids G₂`, and every such hypergraph also avoids the larger `G₁`.
-/
@[category textbook, AMS 5]
theorem erdos_1177.variants.family_avoids_mono
    {W₁ W₂ : Type}
    {G₁ : ThreeUniformHypergraph W₁} {G₂ : ThreeUniformHypergraph W₂}
    (h : G₂.Appears G₁)
    (κ : Cardinal.{0}) :
    FamilyAvoids G₂ κ ⊆ FamilyAvoids G₁ κ := by
  intro ⟨V, X⟩ ⟨hχ, hno⟩
  refine ⟨hχ, fun hG₁ => hno ?_⟩
  exact erdos_1177.variants.appears_trans h hG₁

end Erdos1177
