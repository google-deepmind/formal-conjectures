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

*Reference:* [erdosproblems.com/1177](https://www.erdosproblems.com/1177)

*References:*
- [EGH75] Erdős, P., Galvin, F., Hajnal, A. *On set-systems having large chromatic number
  and not containing prescribed subsystems.* Infinite and finite sets (Colloq., Keszthely,
  1973; dedicated to P. Erdős on his 60th birthday), Vol. I.
  Colloq. Math. Soc. János Bolyai 10, North-Holland (1975), 425–513.
-/

open Cardinal Set
open scoped Cardinal
open Classical

namespace Erdos1177

/-- $\mathcal{F}_G(\kappa)$: the set of pairs $\langle V, H \rangle$ where $V$ is a type and
$H$ is a 3-uniform hypergraph on $V$ with chromatic cardinal exactly $\kappa$ that does not
contain $G$ as a sub-hypergraph. -/
def FamilyAvoids {W : Type} (G : ThreeUniformHypergraph W)
    (κ : Cardinal.{0}) : Set (Σ V : Type, ThreeUniformHypergraph V) :=
  {p | p.2.chromaticCardinal = κ ∧ ¬ G.Appears p.2}

/--
**Erdős–Galvin–Hajnal Problem 1177, Conjecture 1.**

If $\mathcal{F}_G(\aleph_1)$ is non-empty then there exists $X \in \mathcal{F}_G(\aleph_1)$
of cardinality at most $2^{2^{\aleph_0}}$.
-/
@[category research open, AMS 5]
theorem erdos_1177.conjectures.one :
    ∀ {W : Type} [Fintype W] (G : ThreeUniformHypergraph W),
      (FamilyAvoids G (ℵ_ 1)).Nonempty →
      ∃ p ∈ FamilyAvoids G (ℵ_ 1), #p.1 ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ ℵ₀) := by
  sorry

/--
**Erdős–Galvin–Hajnal Problem 1177, Conjecture 2.**

If both $\mathcal{F}_G(\aleph_1)$ and $\mathcal{F}_H(\aleph_1)$ are non-empty then
$\mathcal{F}_G(\aleph_1) \cap \mathcal{F}_H(\aleph_1)$ is non-empty.
-/
@[category research open, AMS 5]
theorem erdos_1177.conjectures.two :
    ∀ {W₁ : Type} [Fintype W₁] (G : ThreeUniformHypergraph W₁)
      {W₂ : Type} [Fintype W₂] (H : ThreeUniformHypergraph W₂),
      (FamilyAvoids G (ℵ_ 1)).Nonempty →
      (FamilyAvoids H (ℵ_ 1)).Nonempty →
      ∃ V : Type, ∃ X : ThreeUniformHypergraph V,
        X.chromaticCardinal = ℵ_ 1 ∧ ¬ G.Appears X ∧ ¬ H.Appears X := by
  sorry

/--
**Erdős–Galvin–Hajnal Problem 1177, Conjecture 3.**

If $\kappa, \mu$ are uncountable cardinals and $\mathcal{F}_G(\kappa)$ is non-empty then
$\mathcal{F}_G(\mu)$ is non-empty.

(We use $\mu$ in place of $\lambda$ to avoid conflict with Lean's reserved `λ` keyword.)
-/
@[category research open, AMS 5]
theorem erdos_1177.conjectures.three :
    ∀ {W : Type} [Fintype W] (G : ThreeUniformHypergraph W)
      (κ μ : Cardinal.{0}),
      ℵ₀ < κ → ℵ₀ < μ →
      (FamilyAvoids G κ).Nonempty →
      (FamilyAvoids G μ).Nonempty := by
  sorry

/--
**Erdős–Galvin–Hajnal Problem 1177 (combined).** The conjunction of Conjectures 1, 2, 3.
-/
@[category research open, AMS 5]
theorem erdos_1177 :
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
**The bound in Conjecture 1**: $\aleph_1 \le 2^{2^{\aleph_0}}$, confirming the bound is
consistent with the chromatic cardinal $\aleph_1$.
-/
@[category test, AMS 5]
example : ℵ_ 1 ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ ℵ₀) := by
  calc ℵ_ 1 ≤ 𝔠 := aleph_one_le_continuum
    _ = (2 : Cardinal) ^ ℵ₀ := two_power_aleph0.symm
    _ ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ ℵ₀) :=
        Cardinal.power_le_power_left (by norm_num) (Cardinal.cantor ℵ₀).le

/--
**Concrete instances for Conjecture 3**: $\aleph_1$ and $\aleph_2$ are both uncountable.
-/
@[category test, AMS 5]
example : ℵ₀ < ℵ_ 1 ∧ ℵ₀ < ℵ_ 2 := by
  constructor
  · rw [← Cardinal.aleph_zero]; exact Cardinal.aleph_lt_aleph.mpr zero_lt_one
  · rw [← Cardinal.aleph_zero]; exact Cardinal.aleph_lt_aleph.mpr (by norm_num)

/--
**Transitivity of `Appears`**: if $G_1$ appears in $G_2$ and $G_2$ appears in $H$, then $G_1$
appears in $H$.
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
**Monotonicity of `FamilyAvoids`**: if $G_2$ appears in $G_1$ then
$\mathcal{F}_{G_2}(\kappa) \subseteq \mathcal{F}_{G_1}(\kappa)$.
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
