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
# Erdős Problem 112

*Reference:* [erdosproblems.com/112](https://www.erdosproblems.com/112)

A problem of Erdős and Rado on directed Ramsey numbers $k(n,m)$: the minimal $k$ such that
any directed graph on $k$ vertices must contain either an independent set of size $n$ or a
transitive tournament of size $m$. Determine $k(n,m)$.

[ErRa67] Erdős, P. and Rado, R., _Partition relations and transitivity domains of binary
relations_, J. London Math. Soc. (1967), 624–633.

[LaMi97] Larson, J. and Mitchell, W., _On a problem of Erdős and Rado_, Ann. Comb. (1997),
245–252.
-/

namespace Erdos112

/-- An oriented graph on vertex type $V$: an irreflexive, antisymmetric binary relation
representing directed edges ($\mathrm{adj}(u, v)$ means there is a directed edge from $u$ to $v$).
Each pair of distinct vertices has at most one directed edge between them. -/
structure Digraph (V : Type*) where
  adj : V → V → Prop
  loopless : ∀ v, ¬ adj v v
  antisymm : ∀ u v, adj u v → ¬ adj v u

/-- An independent set in a directed graph: a set $S$ of vertices with no directed
edges between any two of its members (in either direction). -/
def Digraph.IsIndepSet {V : Type*} (G : Digraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.adj u v

/-- A transitive tournament on vertex set $S$ in directed graph $G$: there is a bijection
$f : \mathrm{Fin}(|S|) \to S$ such that $G.\mathrm{adj}(f(i), f(j))$ holds
if and only if $i < j$. This encodes a total ordering of $S$ compatible with the
edge relation. -/
def Digraph.IsTransTournament {V : Type*} (G : Digraph V) (S : Finset V) : Prop :=
  ∃ f : Fin S.card → {x : V // x ∈ S}, Function.Bijective f ∧
    ∀ i j : Fin S.card, G.adj (f i : V) (f j : V) ↔ i < j

/-- The directed Ramsey number $k(n,m)$: the minimal $k$ such that every directed graph
on $k$ vertices contains either an independent set of size $n$ or a transitive
tournament of size $m$. -/
noncomputable def dirRamseyNum (n m : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (V : Type) [Fintype V], Fintype.card V = k →
    ∀ G : Digraph V,
      (∃ S : Finset V, S.card = n ∧ G.IsIndepSet S) ∨
      (∃ S : Finset V, S.card = m ∧ G.IsTransTournament S)}

/--
Erdős Problem 112: Determine the directed Ramsey number $k(n,m)$.
The exact value is still open.
-/
@[category research open, AMS 5]
theorem erdos_112 :
    ∀ n m : ℕ, 2 ≤ n → 2 ≤ m →
      dirRamseyNum n m = answer(sorry) := by
  sorry

/--
Erdős–Rado upper bound [ErRa67]:
$$k(n,m) \leq \frac{2^{m-1} (n-1)^m + n - 2}{2n - 3}.$$
-/
@[category research solved, AMS 5]
theorem erdos_112.variants.erdos_rado_upper_bound :
    ∀ n m : ℕ, 2 ≤ n → 2 ≤ m →
      dirRamseyNum n m ≤ (2 ^ (m - 1) * (n - 1) ^ m + n - 2) / (2 * n - 3) := by
  sorry

/--
Larson–Mitchell bound [LaMi97]: $k(n, 3) \leq n^2$.
-/
@[category research solved, AMS 5]
theorem erdos_112.variants.larson_mitchell :
    ∀ n : ℕ, 2 ≤ n →
      dirRamseyNum n 3 ≤ n ^ 2 := by
  sorry

/-- The classical 2-color graph Ramsey number $R(n, m)$: the minimal $k$ such that every
2-coloring of the edges of $K_k$ contains either a red clique of size $n$ or a blue clique
of size $m$. -/
noncomputable def graphRamseyNum (n m : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (c : Fin k → Fin k → Bool),
    (∃ S : Finset (Fin k), S.card = n ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c u v = true) ∨
    (∃ S : Finset (Fin k), S.card = m ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c u v = false)}

/-- The 3-color graph Ramsey number $R(a, b, c)$: the minimal $k$ such that every
3-coloring of the edges of $K_k$ contains a monochromatic clique of size $a$, $b$, or $c$
in the respective color. -/
noncomputable def graphRamseyNum3 (a b c : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (col : Fin k → Fin k → Fin 3),
    (∃ S : Finset (Fin k), S.card = a ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → col u v = 0) ∨
    (∃ S : Finset (Fin k), S.card = b ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → col u v = 1) ∨
    (∃ S : Finset (Fin k), S.card = c ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → col u v = 2)}

/--
Ramsey number sandwich (Hunter): $R(n,m) \leq k(n,m) \leq R(n,m,m)$, where $R$ is the
classical graph Ramsey number and $R(n,m,m)$ is the 3-color Ramsey number. The lower bound
holds because any undirected graph can be oriented, and the upper bound holds because the
three options for each pair of vertices (no edge, forward edge, backward edge) correspond
to a 3-coloring.
-/
@[category research solved, AMS 5]
theorem erdos_112.variants.ramsey_sandwich :
    ∀ n m : ℕ, 2 ≤ n → 2 ≤ m →
      graphRamseyNum n m ≤ dirRamseyNum n m ∧
      dirRamseyNum n m ≤ graphRamseyNum3 n m m := by
  sorry

/-- A directed path on vertex set $S$ in directed graph $G$: there is a bijection
$f : \mathrm{Fin}(|S|) \to S$ such that $G.\mathrm{adj}(f(i), f(i+1))$ holds for all
consecutive indices. Unlike a transitive tournament, only consecutive vertices need to
be connected. -/
def Digraph.IsDirectedPath {V : Type*} (G : Digraph V) (S : Finset V) : Prop :=
  ∃ f : Fin S.card → {x : V // x ∈ S}, Function.Bijective f ∧
    ∀ i : Fin S.card, ∀ h : (i : ℕ) + 1 < S.card,
      G.adj (f i : V) (f ⟨i + 1, h⟩ : V)

/-- The directed path Ramsey number: the minimal $k$ such that every directed graph on $k$
vertices contains either an independent set of size $n$ or a directed path of size $m$. -/
noncomputable def dirPathRamseyNum (n m : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (V : Type) [Fintype V], Fintype.card V = k →
    ∀ G : Digraph V,
      (∃ S : Finset V, S.card = n ∧ G.IsIndepSet S) ∨
      (∃ S : Finset V, S.card = m ∧ G.IsDirectedPath S)}

/--
Hunter–Steiner result: replacing "transitive tournament" with "directed path" in the
definition of $k(n,m)$ yields the exact answer $k(n,m) = (n-1)(m-1) + 1$.
-/
@[category research solved, AMS 5]
theorem erdos_112.variants.hunter_steiner :
    ∀ n m : ℕ, 2 ≤ n → 2 ≤ m →
      dirPathRamseyNum n m = (n - 1) * (m - 1) + 1 := by
  sorry

end Erdos112
