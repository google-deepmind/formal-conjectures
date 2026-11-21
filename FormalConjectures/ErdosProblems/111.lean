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

public import FormalConjecturesUtil

/-!
# Erdős Problem 111

*References:*
- [erdosproblems.com/111](https://www.erdosproblems.com/111)
- [Er81] Erdős, P., On the combinatorial problems which I would most like to see solved. (1981)
- [EHS82] Erdős, P., Hajnal, A., and Szemerédi, E., On almost bipartite large chromatic graphs.
  Theory and practice of combinatorics (1982), 117–123.
- [Er87] Erdős, P., Some problems on finite and infinite graphs. (1987)
- [Er90] Erdős, P., Some of my favourite unsolved problems. (1990)
- [Er97d] Erdős, P., Some recent problems and results in graph theory. (1997)
- [Er97f] Erdős, P., Some unsolved problems. (1997)

See also Erdős Problem [74].

## Formalization notes

- **`bipartiteDistance G`**: the minimum number of edges to delete from a (finite) simple graph $G$
  to make it bipartite. Defined as the infimum over all spanning subgraphs $H \leq G$ with
  `H.IsBipartite` of the number of edges in `G.edgeSet \ H.edgeSet`.

- **`hG G n`**: for a graph $G$ on vertex type $V$, `hG G n` is the supremum over all sets $S$ of
  vertices of cardinality $n$ of `bipartiteDistance (G.induce S)`. This matches the problem's
  formulation: "any subgraph of $G$ on $n$ vertices can be made bipartite after deleting at most
  $h_G(n)$ edges."
-/

@[expose] public section

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
$h_G(n)/n$ tends to infinity: for every constant $C$, all sufficiently large $n$ satisfy
$h_G(n) > C \cdot n$.
-/
@[category research open, question, AMS 5]
theorem erdos_111 :
    ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
      Filter.Tendsto (fun n : ℕ => (hG G n : ℝ) / n) Filter.atTop Filter.atTop := by
  sorry

/- ## Variants and known partial results -/

/--
**Linear lower bound (ZFC, [EHS82])**: Every graph $G$ with chromatic number $\aleph_1$ has
$h_G(n) \geq c \cdot n$ for some positive constant $c > 0$ and all sufficiently large $n$
(i.e., the *linear* lower bound $h_G(n) \gg n$ is known).

This follows from the fact that every graph with uncountable chromatic number contains
$\aleph_1$ vertex-disjoint odd cycles of some fixed odd length $\ell$: any induced subgraph
on $n$ vertices containing $\gg n / \ell$ such cycles requires removing $\gg n$ edges to
become bipartite.

This is a *strictly weaker* statement than the headline `erdos_111`, which asks for
$h_G(n)/n \to \infty$ (i.e., $h_G(n)$ grows *super-linearly* — the constant `c` could be
taken arbitrarily large for a fixed graph $G$). Whether the linear lower bound can be
improved to super-linear remains the open question.
-/
@[category research solved, AMS 5]
theorem erdos_111.variants.lower_bound :
    ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in Filter.atTop, c * n ≤ hG G n := by
  sorry

/--
**Upper bound existence (Erdős-Hajnal-Szemerédi [EHS82])**: There exists a graph $G$ with
chromatic number $\aleph_1$ such that $h_G(n) \ll n^{3/2}$, i.e., there is a constant $C > 0$
with $h_G(n) \leq C \cdot n^{3/2}$ for all $n$.
-/
@[category research solved, AMS 5]
theorem erdos_111.variants.upper_bound_existence :
    ∃ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 ∧
      (fun n : ℕ => (hG G n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  sorry

/--
Erdős conjectured [Er81] that for every $\varepsilon > 0$ there is a graph $G$ with
$\chi(G) = \aleph_1$ such that $h_G(n) \ll n^{1+\varepsilon}$.
The graph is chosen after $\varepsilon$.
-/
@[category research open, AMS 5]
theorem erdos_111.variants.erdos_conjecture :
    ∀ ε : ℝ, 0 < ε → ∃ (V : Type) (G : SimpleGraph V),
      G.chromaticCardinal = ℵ_ 1 ∧
        (fun n : ℕ => (hG G n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 + ε)) := by
  sorry

end Erdos111
