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
# Erdős Problem 60

*Reference:* [erdosproblems.com/60](https://www.erdosproblems.com/60)

Does every graph on $n$ vertices with more than $\mathrm{ex}(n; C_4)$ edges contain
$\gg n^{1/2}$ many copies of $C_4$?

Conjectured by Erdős and Simonovits [Er90][Er93], who could not even prove that
at least 2 copies of $C_4$ are guaranteed. The behaviour of $\mathrm{ex}(n; C_4)$
is the subject of problem [765].

[Er90] Erdős, P. (1990).

[Er93] Erdős, P. (1993).
-/

open SimpleGraph Classical

namespace Erdos60

/-- The cycle graph $C_m$ on $m$ vertices ($m \geq 3$). -/
def cycleGraph60 (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/-- $G$ contains $H$ as a subgraph (via an injective homomorphism). -/
def ContainsSubgraph60 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- $\mathrm{ex}(n; H)$: maximum number of edges in an $H$-free simple graph on $n$ vertices. -/
noncomputable def extremalNumber60 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph60 G H ∧ G.edgeSet.ncard = m}

/-- The number of labeled copies of $C_4$ in $G$: injective maps $f : \mathrm{Fin}\, 4 \to \mathrm{Fin}\, n$
preserving $C_4$ adjacency. Each unordered $C_4$ subgraph yields $8$ labeled copies
($4$ rotations $\times$ $2$ reflections). -/
noncomputable def labeledC4Count (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter (fun (f : Fin 4 → Fin n) =>
    Function.Injective f ∧
    ∀ i : Fin 4, G.Adj (f i) (f (i + 1)))).card

/--
Erdős Problem 60 [Er90][Er93]:

Does every graph on $n$ vertices with more than $\mathrm{ex}(n; C_4)$ edges contain
$\gg n^{1/2}$ copies of $C_4$?

Formally: there exist $c > 0$ and $N_0$ such that for all $n \geq N_0$, every graph $G$ on
$n$ vertices with more than $\mathrm{ex}(n; C_4)$ edges has at least $c \cdot n^{1/2}$ labeled
copies of $C_4$.
-/
@[category research open, AMS 5]
theorem erdos_60 : answer(sorry) ↔
    ∃ (c : ℝ) (_ : c > 0) (N₀ : ℕ),
    ∀ n : ℕ, N₀ ≤ n →
    ∀ G : SimpleGraph (Fin n),
      G.edgeSet.ncard > extremalNumber60 (cycleGraph60 4 (by omega)) n →
      (labeledC4Count n G : ℝ) ≥ c * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

end Erdos60
