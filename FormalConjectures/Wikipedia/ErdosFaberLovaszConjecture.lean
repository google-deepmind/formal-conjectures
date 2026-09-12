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
# The Erdős–Faber–Lovász conjecture (1972)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Faber%E2%80%93Lov%C3%A1sz_conjecture)
* [Er81] Erdős, P. (1981). "On the combinatorial problems which I would most like to see solved."
  *Combinatorica* 1, pp. 25--42.
* [Ka92] Kahn, J. (1992). "Coloring nearly-disjoint hypergraphs with $n + o(n)$ colors."
  *J. Combin. Theory Ser. A* 59, pp. 31--39.
* [CL88] Chang, W. I. and Lawler, E. L. (1988). "Edge coloring of hypergraphs and a conjecture
  of Erdős, Faber, Lovász." *Combinatorica* 8, pp. 293--295.
* [KKKMO23] Kang, D. Y., Kelly, T., Kühn, D., Methuku, A. and Osthus, D. (2023). "A proof of the
  Erdős–Faber–Lovász conjecture." *Ann. of Math.* 198, pp. 537--618.
  [arXiv:2101.04698](https://arxiv.org/abs/2101.04698)
-/

open SimpleGraph

namespace ErdosFaberLovaszConjecture

variable {V : Type*}

/-- The complete graph on the vertex set `S ⊆ V`, viewed as a graph on all of `V` (vertices
outside `S` are isolated). -/
def cliqueOn (S : Finset V) : SimpleGraph V :=
  fromEdgeSet {e : Sym2 V | ∀ v ∈ e, v ∈ S}

/-- A family of `n` cliques `S₀, …, Sₙ₋₁ ⊆ V`, each of size `n`, any two of which share at most
one vertex. -/
structure IsEFLFamily [DecidableEq V] (n : ℕ) (S : Fin n → Finset V) : Prop where
  card_eq : ∀ i, (S i).card = n
  inter_le_one : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1

/-- The union of the cliques of the family `S`: the graph in which two vertices are adjacent
iff they lie in a common `S i`. -/
def unionGraph {n : ℕ} (S : Fin n → Finset V) : SimpleGraph V :=
  ⨆ i, cliqueOn (S i)

/--
**The Erdős–Faber–Lovász conjecture (1972; proved for all large $n$ by Kang, Kelly, Kühn,
Methuku and Osthus, 2023).**

If a graph is the union of $n$ cliques, each with $n$ vertices, such that any two of the cliques
share at most one vertex, then the graph is $n$-colourable.

Equivalently (in hypergraph language): every linear hypergraph with $n$ vertices has chromatic
index at most $n$. The statement is known for all sufficiently large $n$ [KKKMO23]; whether it
holds for *every* $n$ remains open.
-/
@[category research open, AMS 5]
theorem erdos_faber_lovasz_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (n : ℕ) (S : Fin n → Finset V),
      IsEFLFamily n S → (unionGraph S).Colorable n := by
  sorry

/--
**Kang–Kelly–Kühn–Methuku–Osthus (2023): the conjecture holds for all sufficiently large $n$.**

*Reference:* [KKKMO23].
-/
@[category research solved, AMS 5]
theorem erdos_faber_lovasz_conjecture.variants.large_n :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (n : ℕ), n₀ ≤ n →
      ∀ S : Fin n → Finset V, IsEFLFamily n S → (unionGraph S).Colorable n := by
  sorry

/--
**Chang–Lawler (1988): $\lceil 3n/2 - 2 \rceil$ colours always suffice.**

*Reference:* [CL88].
-/
@[category research solved, AMS 5]
theorem erdos_faber_lovasz_conjecture.variants.chang_lawler
    {V : Type} [Fintype V] [DecidableEq V] (n : ℕ) (S : Fin n → Finset V)
    (hS : IsEFLFamily n S) :
    (unionGraph S).Colorable ((3 * n - 3) / 2) := by
  sorry

/--
**Kahn (1992): $n + o(n)$ colours suffice.**

For every $\varepsilon > 0$ there is $n_0$ such that for all $n \ge n_0$ every Erdős–Faber–Lovász
family of $n$ cliques is $\lfloor (1 + \varepsilon) n \rfloor$-colourable.

*Reference:* [Ka92].
-/
@[category research solved, AMS 5]
theorem erdos_faber_lovasz_conjecture.variants.kahn :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (n : ℕ), n₀ ≤ n →
      ∀ S : Fin n → Finset V, IsEFLFamily n S →
        (unionGraph S).Colorable ⌊(1 + ε) * n⌋₊ := by
  sorry

/-- Adjacency in `cliqueOn S`: two distinct vertices of `S`. -/
@[category API, AMS 5]
lemma cliqueOn_adj {S : Finset V} {u v : V} :
    (cliqueOn S).Adj u v ↔ (u ∈ S ∧ v ∈ S) ∧ u ≠ v := by
  simp [cliqueOn, fromEdgeSet_adj, Sym2.mem_iff, forall_eq_or_imp]

/--
**The case `n = 1` of the conjecture.**

With `n = 1` the family consists of a single vertex, so the union graph has no edges and is
`1`-colourable.
-/
@[category test, AMS 5]
theorem erdos_faber_lovasz_conjecture.variants.one
    {V : Type} [Fintype V] [DecidableEq V] (S : Fin 1 → Finset V) (hS : IsEFLFamily 1 S) :
    (unionGraph S).Colorable 1 := by
  refine ⟨⟨fun _ => 0, fun {u v} huv => ?_⟩⟩
  exfalso
  rw [unionGraph, iSup_adj] at huv
  obtain ⟨i, hi⟩ := huv
  rw [cliqueOn_adj] at hi
  obtain ⟨⟨hu, hv⟩, hne⟩ := hi
  have h1 := hS.card_eq i
  exact hne (Finset.card_le_one.mp h1.le u hu v hv)

end ErdosFaberLovaszConjecture
