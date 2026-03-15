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
# Erdős Problem 737

*Reference:* [erdosproblems.com/737](https://www.erdosproblems.com/737)

Let $G$ be a graph with chromatic number $\aleph_1$. Must there exist an
edge $e$ such that, for all large $n$, $G$ contains a cycle of length $n$
containing $e$?

A problem of Erdős, Hajnal, and Shelah [EHS74], who proved that $G$ must
contain all sufficiently large cycles (see [594]).

This is true, and was proved by Thomassen [Th83].

## References

[EHS74] Erdős, P., Hajnal, A., and Shelah, S., *On some general properties of chromatic numbers*.
Topics in topology (Proc. Colloq., Keszthely, 1972), Colloq. Math. Soc. Janos Bolyai (1974),
243-255.

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_,
Combinatorica **1** (1981), 25–42.

[Th83] Thomassen, C., _Cycles in graphs of uncountable chromatic number_,
Combinatorica **3** (1983), 133–134.
-/

open SimpleGraph

namespace Erdos737

/-- A graph has uncountable chromatic number: it cannot be properly colored
    with countably many colors. -/
def HasUncountableChromaticNumber {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (α : Type*) [Countable α], IsEmpty (G.Coloring α)

/-- The cycle graph $C_m$ on $m$ vertices ($m \geq 3$). Vertex $i$ is adjacent to vertex
    $i + 1 \pmod{m}$ and vertex $i - 1 \pmod{m}$. -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/-- $G$ contains a copy of the cycle graph $C_m$ passing through edge $\{u, v\}$:
    there is an injective embedding of $C_m$ into $G$ that maps some edge of
    the cycle to the edge $\{u, v\}$. -/
def ContainsCycleThroughEdge {V : Type*}
    (G : SimpleGraph V) (u v : V) (m : ℕ) (hm : m ≥ 3) : Prop :=
  ∃ f : Fin m → V, Function.Injective f ∧
    (∀ a b : Fin m, (cycleGraph m hm).Adj a b → G.Adj (f a) (f b)) ∧
    ∃ a b : Fin m, (cycleGraph m hm).Adj a b ∧
      ((f a = u ∧ f b = v) ∨ (f a = v ∧ f b = u))

/--
Erdős Problem 737 [EHS74] [Er81]:

If $G$ is a graph with chromatic number $\geq \aleph_1$ (uncountable), then there
exists an edge $\{u, v\}$ of $G$ such that for all sufficiently large $n$,
$G$ contains a cycle of length $n$ passing through $\{u, v\}$.

Proved by Thomassen [Th83].
-/
@[category research solved, AMS 5]
theorem erdos_737 : answer(True) ↔
    ∀ {V : Type*} (G : SimpleGraph V),
      HasUncountableChromaticNumber G →
        ∃ u v : V, G.Adj u v ∧
          ∃ N₀ : ℕ, ∀ (n : ℕ) (hn : n ≥ 3), n ≥ N₀ →
            ContainsCycleThroughEdge G u v n hn := by
  sorry

end Erdos737
