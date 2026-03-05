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
# Erdős Problem 630

*Reference:* [erdosproblems.com/630](https://www.erdosproblems.com/630)

Erdős, Rubin, and Taylor asked whether every planar bipartite graph is 3-choosable
(i.e., 3-list-colorable). This was proved by Alon and Tarsi.

[ERT80] Erdős, P., Rubin, A. L., and Taylor, H., _Choosability in graphs_. Proceedings of the
West Coast Conference on Combinatorics, Graph Theory and Computing (1980).

[AlTa92] Alon, N. and Tarsi, M., _Colorings and orientations of graphs_. Combinatorica 12
(1992), 125-134.
-/

open SimpleGraph

namespace Erdos630

/-- A proper list coloring of $G$ with respect to a list assignment $L : V \to \text{Finset}\ \mathbb{N}$
is a function $f : V \to \mathbb{N}$ such that $f(v) \in L(v)$ for all $v$, and $f(u) \neq f(v)$
whenever $u$ and $v$ are adjacent. -/
def IsProperListColoring {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ)
    (f : V → ℕ) : Prop :=
  (∀ v, f v ∈ L v) ∧ (∀ u v, G.Adj u v → f u ≠ f v)

/-- A graph $G$ is $k$-choosable ($k$-list-colorable) if for every list assignment $L$
where each vertex receives a list of at least $k$ colors, there exists a
proper list coloring. -/
def IsChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) →
    ∃ f : V → ℕ, IsProperListColoring G L f

/-- The list chromatic number (choice number) of a graph $G$: the minimum $k$
such that $G$ is $k$-choosable. -/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsChoosable G k}

/-- A graph is planar if it can be embedded in the plane without edge crossings.
Mathlib does not yet have a formalization of graph planarity; we axiomatize it
here as an opaque predicate. -/
opaque IsPlanar {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop

/--
Erdős Problem 630 [ERT80]:

Every planar bipartite graph $G$ is $3$-choosable, i.e., $\chi_L(G) \leq 3$.

Proved by Alon and Tarsi [AlTa92].
-/
@[category research solved, AMS 5]
theorem erdos_630 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hplanar : IsPlanar G) (hbip : G.Colorable 2) :
    IsChoosable G 3 := by
  sorry

end Erdos630
