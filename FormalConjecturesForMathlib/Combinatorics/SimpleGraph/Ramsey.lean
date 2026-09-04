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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Nat.Lattice
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.EdgeColouring

@[expose] public section

/-!
# Ramsey-type properties of graph pairs

The Erdős–Hajnal "exceptional pair" trio of predicates:

- `HasFiniteRamseyProperty G₁ G₂` — for every `n ≥ 1` there is a `G₁`-free graph `H` such
  that every `n`-edge-colouring of `H` contains a monochromatic `G₂`.
- `HasCountableRamseyEscape G₁ G₂` — every `G₁`-free graph `H` admits a countable
  edge-colouring with every colour class `G₂`-free.
- `IsErdosHajnalExceptional G₁ G₂` — the conjunction of both.

These were introduced for Erdős Problem 596 but are reusable for Problem 595 and other
Ramsey-type questions; we factor them out per mo271's review.
-/

namespace SimpleGraph

/-- The **finite Ramsey property** for the pair $(G_1, G_2)$: for every $n \geq 1$, there
exists a $G_1$-free graph `H` on some vertex type in `Type` (universe 0) such that every
`n`-edge-colouring of `H` contains a monochromatic copy of `G_2`. -/
def HasFiniteRamseyProperty {U₁ U₂ : Type*}
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∃ (V : Type) (H : SimpleGraph V),
    G₁.Free H ∧
    ∀ (c : Fin n → SimpleGraph V), H.IsEdgeColouring c →
      ∃ i, G₂ ⊑ c i

/-- The **countable Ramsey escape property** for the pair $(G_1, G_2)$: every $G_1$-free
graph `H` on a `Type`-valued vertex type has a countable edge-colouring in which every
colour class is $G_2$-free. -/
def HasCountableRamseyEscape {U₁ U₂ : Type*}
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) : Prop :=
  ∀ (W : Type) (H : SimpleGraph W),
    G₁.Free H →
    ∃ (d : ℕ → SimpleGraph W),
      H.IsEdgeColouring d ∧ ∀ j, G₂.Free (d j)

/-- A pair $(G_1, G_2)$ is **Erdős–Hajnal exceptional** if it has both the finite Ramsey
property and the countable Ramsey escape property. -/
def IsErdosHajnalExceptional {U₁ U₂ : Type*}
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) : Prop :=
  HasFiniteRamseyProperty G₁ G₂ ∧ HasCountableRamseyEscape G₁ G₂

/-- The **Ramsey number** of a pair of graphs $(G, H)$: the least `N` such that every
`SimpleGraph (Fin N)` — the "red" graph of a two-colouring of $K_N$ — either contains a copy of
`G` (a red `G`) or contains a copy of `H` in its complement (a blue `H`). -/
noncomputable def ramseyNumber {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf {N : ℕ | ∀ F : SimpleGraph (Fin N), G ⊑ F ∨ H ⊑ Fᶜ}

/-- The defining set of `ramseyNumber` is **upward closed**: if every red graph on `Fin N`
contains a red `G` or a blue `H`, then so does every red graph on any larger `Fin N'`. Restrict a
red graph `F'` on `Fin N'` to its first `N` vertices via `Fin.castLEEmb` (giving the induced
subgraph `F'.comap f ↪g F'`), apply the hypothesis for `N`, and transport the resulting red copy of
`G` — or the blue copy of `H`, using `(F'.comap f)ᶜ = F'ᶜ.comap f` — back up along that embedding. -/
theorem ramseyNumber_setOf_upward_closed {α β : Type*}
    (G : SimpleGraph α) (H : SimpleGraph β) :
    ∀ N ∈ {N : ℕ | ∀ F : SimpleGraph (Fin N), G ⊑ F ∨ H ⊑ Fᶜ},
      ∀ N', N ≤ N' → N' ∈ {N : ℕ | ∀ F : SimpleGraph (Fin N), G ⊑ F ∨ H ⊑ Fᶜ} := by
  intro N hN N' hNN' F'
  set f : Fin N ↪ Fin N' := Fin.castLEEmb hNN' with hf
  -- The induced subgraph on the first `N` vertices embeds into `F'`.
  have embF : (F'.comap f) ↪g F' := SimpleGraph.Embedding.comap f F'
  -- Complement commutes with `comap` along an injection, so the complement embeds too.
  have hcc : (F'.comap f)ᶜ = F'ᶜ.comap f := by
    ext a b
    simp only [compl_adj, comap_adj, f.injective.ne_iff]
  rcases hN (F'.comap f) with hG | hH
  · exact Or.inl (hG.trans ⟨embF.toCopy⟩)
  · rw [hcc] at hH
    exact Or.inr (hH.trans ⟨(SimpleGraph.Embedding.comap f F'ᶜ).toCopy⟩)

end SimpleGraph
