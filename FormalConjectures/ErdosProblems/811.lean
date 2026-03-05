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
# Erdős Problem 811

*Reference:* [erdosproblems.com/811](https://www.erdosproblems.com/811)

Suppose $n \equiv 1 \pmod{m}$. We say that an edge-colouring of $K_n$ using $m$ colours
is balanced if every vertex sees exactly $\lfloor n/m \rfloor$ edges of each colour.

For which graphs $G$ is it true that, if $m = e(G)$, for all large $n \equiv 1 \pmod{m}$,
every balanced edge-colouring of $K_n$ with $m$ colours contains a rainbow copy
of $G$? (That is, a subgraph isomorphic to $G$ where each edge receives a
different colour.)

A problem of Erdős, Pyber, and Tuza.

[Er91] Erdős, P., _Some of my favourite problems in various branches of combinatorics_, 1991.

[ErTu93] Erdős, P. and Tuza, Zs., _Rainbow subgraphs in edge-colorings of complete graphs_, 1993.

[Er96] Erdős, P., _Some recent problems and results in graph theory_, 1996.

[ClWa23] Clemen, F. and Wagner, A., 2023.

[AxCl24] Axenovich, M. and Clemen, F., 2024.
-/

open SimpleGraph Finset

namespace Erdos811

/-- The cycle graph on $m$ vertices (for $m \ge 3$): vertex $i$ is adjacent
    to vertices $(i+1) \bmod m$ and $(i-1) \bmod m$. -/
def cycleGraph811 (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/-- An edge-colouring of the complete graph on $\operatorname{Fin} n$ with $m$ colours is
    **balanced** if every vertex sees exactly $\lfloor n / m \rfloor$ edges of each colour.
    (When $n \equiv 1 \pmod{m}$, the degree $n - 1$ divides evenly as
    $m \cdot \lfloor n / m \rfloor$.) -/
def IsBalancedColoring (n m : ℕ) (c : Sym2 (Fin n) → Fin m) : Prop :=
  ∀ (v : Fin n) (i : Fin m),
    (Finset.univ.filter (fun w : Fin n => w ≠ v ∧
      c (Sym2.mk (v, w)) = i)).card = n / m

/-- A **rainbow copy** of a graph $G$ in a coloured complete graph on $\operatorname{Fin} n$
    is an injective vertex map such that all edges of $G$ receive pairwise
    distinct colours. -/
def HasRainbowCopy {V : Type*} (G : SimpleGraph V)
    {n m : ℕ} (c : Sym2 (Fin n) → Fin m) : Prop :=
  ∃ f : V → Fin n, Function.Injective f ∧
    ∀ a b a' b' : V, G.Adj a b → G.Adj a' b' →
      Sym2.mk (a, b) ≠ Sym2.mk (a', b') →
      c (Sym2.mk (f a, f b)) ≠ c (Sym2.mk (f a', f b'))

/--
**Erdős Problem 811** (specific challenge from [Er91] and [Er96]):

For all sufficiently large $n \equiv 1 \pmod{6}$, every balanced edge-colouring
of $K_n$ with $6$ colours contains a rainbow copy of $C_6$.

The companion question about $K_4$ (which also has $6$ edges) was answered
negatively by Clemen and Wagner [ClWa23].
-/
@[category research open, AMS 5]
theorem erdos_811 :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → n % 6 = 1 →
      ∀ c : Sym2 (Fin n) → Fin 6,
        IsBalancedColoring n 6 c →
        HasRainbowCopy (cycleGraph811 6 (by omega)) c := by
  sorry

end Erdos811
