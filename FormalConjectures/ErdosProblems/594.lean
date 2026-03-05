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
# Erdős Problem 594

*Reference:* [erdosproblems.com/594](https://www.erdosproblems.com/594)

A problem of Erdős and Hajnal: does every graph with chromatic number
$\geq \aleph_1$ contain all sufficiently large odd cycles? Proved by
Erdős, Hajnal, and Shelah [EHS74].

[ErHa66] Erdős, P. and Hajnal, A., *On chromatic number of graphs and
set-systems*, Acta Math. Acad. Sci. Hung. **17** (1966), 61–99.

[Er69b] Erdős, P., *Problems and results in combinatorial analysis and
graph theory*, Proof Techniques in Graph Theory (1969), 27–35.

[EHS74] Erdős, P., Hajnal, A., and Shelah, S., *On some general properties
of chromatic numbers*, Topics in Topology, Colloq. Math. Soc. Janos Bolyai
**8** (1974), 243–255.
-/

open SimpleGraph Cardinal

namespace Erdos594

/-- A graph has uncountable chromatic number: it cannot be properly colored
with countably many colors. -/
def HasUncountableChromaticNumber {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (α : Type*) [Countable α], IsEmpty (G.Coloring α)

/-- The cycle graph $C_m$ on $m$ vertices ($m \geq 3$). Vertex $i$ is adjacent to vertex
$i + 1 \pmod{m}$ and vertex $i - 1 \pmod{m}$. -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ h => h.1 rfl

/-- $G$ contains a copy of $H$: there is an injective map preserving adjacency. -/
def ContainsCopy {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ u v, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Problem 594 [ErHa66] [Er69b]:

Every graph with uncountable chromatic number (i.e., chromatic number
$\geq \aleph_1$) contains all sufficiently large odd cycles. That is, there exists
$N_0$ such that for all odd $n \geq N_0$ (with $n \geq 3$), the graph contains $C_n$
as a subgraph.

Proved by Erdős, Hajnal, and Shelah [EHS74].
-/
@[category research solved, AMS 5]
theorem erdos_594 : answer(True) ↔
    ∀ {V : Type*} (G : SimpleGraph V),
      HasUncountableChromaticNumber G →
      ∃ N₀ : ℕ, ∀ (n : ℕ) (hn : n ≥ 3), Odd n → n ≥ N₀ →
        ContainsCopy G (cycleGraph n hn) := by
  sorry

end Erdos594
