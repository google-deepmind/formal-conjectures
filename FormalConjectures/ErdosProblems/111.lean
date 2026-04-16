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
# Erdős Problem 111

*Reference:* [erdosproblems.com/111](https://www.erdosproblems.com/111)

*References:*
- [Er81] Erdős, P., Some combinatorial problems in graph theory. (1981)
- [EHS82] Erdős, P., Hajnal, A., and Szemerédi, E., On almost bipartite large chromatic graphs.
  Annals of Discrete Math. (1982), 117–123.
- [Er87] Erdős, P., Problems and results on chromatic numbers in finite and infinite graphs. (1987)
- [Er90] Erdős, P., Some of my favourite problems in various branches of combinatorics. (1990)
- [Er97d] Erdős, P., Some problems on elementary geometry. (1997)
- [Er97f] Erdős, P., Some of my favourite unsolved problems. (1997)

## Problem statement

If $G$ is a graph, let $h_G(n)$ be defined such that any subgraph of $G$ on $n$ vertices can be
made bipartite after deleting at most $h_G(n)$ edges.

What is the behaviour of $h_G(n)$? Is it true that $h_G(n)/n \to \infty$ for every graph $G$
with chromatic number $\aleph_1$?

This is a problem of Erdős, Hajnal, and Szemerédi [EHS82].

## Known results

- **Lower bound**: $h_G(n) \gg n$ — this holds (with $h_G(n)/n \to \infty$) since every graph
  with chromatic number $\geq \aleph_1$ contains $\aleph_1$ many vertex-disjoint odd cycles of
  some fixed length. (Verified in ZFC.)
- **Upper bound**: Erdős, Hajnal, and Szemerédi [EHS82] constructed a graph $G$ with chromatic
  number $\aleph_1$ for which $h_G(n) \ll n^{3/2}$.
- **Erdős conjecture**: For every $\varepsilon > 0$, there exists $C(\varepsilon) > 0$ such that
  $h_G(n) \leq C(\varepsilon) \cdot n^{1+\varepsilon}$ for every graph $G$ with chromatic number
  $\geq \aleph_1$ and every $n$.

## Formalization notes

- **`bipartiteDistance G`**: the minimum number of edges to delete from a (finite) simple graph $G$
  to make it bipartite. Defined as the infimum over all spanning subgraphs $H \leq G$ with
  `H.IsBipartite` of the number of edges in `G.edgeSet \ H.edgeSet`.

- **`hG G n`**: for a graph $G$ on vertex type $V$, `hG G n` is the supremum over all sets $S$ of
  vertices of cardinality $n$ of `bipartiteDistance (G.induce S)`. This matches the problem's
  formulation: "any subgraph of $G$ on $n$ vertices can be made bipartite after deleting at most
  $h_G(n)$ edges."

- The main question asks whether `hG G n / n → ∞` for every $G$ with `G.chromaticCardinal = ℵ₁`.
  We formalize this as: the ratio `hG G n / n` is not bounded, i.e., for every $C$, there exists
  $n$ with `hG G n > C * n`.
-/

open Filter Asymptotics Cardinal SimpleGraph Set

namespace Erdos111

/-- The **bipartite distance** of a finite simple graph `G`: the minimum number of edges
that must be deleted from `G` to make it bipartite.

Formally, this is the infimum of `Set.ncard (G.edgeSet \ H.edgeSet)` over all spanning
subgraphs `H ≤ G` (as relations on the same vertex set) such that `H` is bipartite. -/
noncomputable def bipartiteDistance {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
    Set.ncard (G.edgeSet \ H.edgeSet) = k}

/-- The function $h_G(n)$: for a graph $G$ on vertex type $V$, `hG G n` is the supremum over
all sets $S \subseteq V$ with $|S| = n$ of the bipartite distance of the induced subgraph on $S$.

This captures the problem's notion: "any subgraph of $G$ on $n$ vertices can be made bipartite
after deleting at most $h_G(n)$ edges." -/
noncomputable def hG {V : Type*} (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Set V, S.ncard = n ∧ bipartiteDistance (G.induce S) = k}

/- ## Main open problem -/

/--
**Erdős Problem 111** (Erdős, Hajnal, Szemerédi [EHS82]):

If $G$ is a graph with chromatic number $\aleph_1$, is it true that $h_G(n)/n \to \infty$?

Formally: for every graph $G$ (on a type $V$) with chromatic cardinal $\aleph_1$, the ratio
$h_G(n)/n$ is unbounded, i.e., for every constant $C$, there are arbitrarily large $n$ such
that $h_G(n) > C \cdot n$.
-/
@[category research open, AMS 5]
theorem erdos_111 : answer(sorry) ↔
    ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
      ∀ C : ℝ, ∃ n : ℕ, 0 < n ∧ C * n < hG G n := by
  sorry

/- ## Variants and known partial results -/

/--
**Lower bound (ZFC)**: Every graph $G$ with chromatic number $\geq \aleph_1$ satisfies
$h_G(n) > 0$ for all sufficiently large $n$, and moreover $h_G(n)$ grows without bound.

The stronger form: $h_G(n)/n$ is not bounded above by any constant — there exist arbitrarily
large $n$ with $h_G(n) > n / 2$.

This follows from the fact that every graph with uncountable chromatic number contains
$\aleph_1$ vertex-disjoint odd cycles of some fixed odd length $\ell$: any induced subgraph
on $n$ vertices containing $\gg n / \ell$ such cycles requires removing $\gg n$ edges to
become bipartite.
-/
@[category research solved, AMS 5]
theorem erdos_111.variants.lower_bound :
    ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
      ∀ C : ℝ, ∃ n : ℕ, 0 < n ∧ C * n < hG G n := by
  sorry

/--
**Upper bound existence (Erdős-Hajnal-Szemerédi [EHS82])**: There exists a graph $G$ with
chromatic number $\aleph_1$ such that $h_G(n) \ll n^{3/2}$, i.e., there is a constant $C > 0$
with $h_G(n) \leq C \cdot n^{3/2}$ for all $n$.

This shows that Erdős's conjecture (if true) would be essentially tight in its exponent:
the true exponent lies in $(1, 3/2]$.
-/
@[category research solved, AMS 5]
theorem erdos_111.variants.upper_bound_existence :
    ∃ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 ∧
      (fun n : ℕ => (hG G n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  sorry

/--
**Erdős conjecture (stronger upper bound)**: For every graph $G$ with chromatic number $\aleph_1$
and every $\varepsilon > 0$, the function $h_G(n)$ satisfies $h_G(n) \ll_\varepsilon n^{1+\varepsilon}$.

That is, for every $\varepsilon > 0$ there exists $C(\varepsilon) > 0$ such that for every graph
$G$ with $\chi(G) = \aleph_1$, we have $h_G(n) \leq C(\varepsilon) \cdot n^{1 + \varepsilon}$
for all $n$.

This conjecture (if true) would mean that $h_G(n)$ grows only barely super-linearly.
-/
@[category research open, AMS 5]
theorem erdos_111.variants.erdos_conjecture : answer(sorry) ↔
    ∀ (ε : ℝ), 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
          ∀ n : ℕ, (hG G n : ℝ) ≤ C * (n : ℝ) ^ (1 + ε) := by
  sorry

end Erdos111
