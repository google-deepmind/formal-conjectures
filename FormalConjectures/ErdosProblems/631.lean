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
# Erdős Problem 631

*Reference:* [erdosproblems.com/631](https://www.erdosproblems.com/631)

The list chromatic number $\chi_L(G)$ is defined to be the minimal $k$ such that for any
assignment of a list of $k$ colours to each vertex of $G$ (perhaps different lists for
different vertices) a colouring of each vertex by a colour on its list can be chosen
such that adjacent vertices receive distinct colours.

A problem of Erdős, Rubin, and Taylor [ERT80]. Thomassen [Th94] proved that
$\chi_L(G) \leq 5$ if $G$ is planar, and Voigt [Vo93] constructed a planar graph
with $\chi_L(G) = 5$.

[ERT80] Erdős, P., Rubin, A. L., and Taylor, H., _Choosability in graphs_.
Proceedings of the West Coast Conference on Combinatorics, Graph Theory and
Computing, Humboldt State Univ., Arcata, Calif. (1980), 125–157.

[Th94] Thomassen, C., _Every planar graph is 5-choosable_.
Journal of Combinatorial Theory, Series B 62 (1994), 180–181.

[Vo93] Voigt, M., _List colourings of planar graphs_.
Discrete Mathematics 120 (1993), 215–219.

[Gu96] Gutner, S., _The complexity of planar graph choosability_.
Discrete Mathematics (1996), 119–130.
-/

open SimpleGraph

namespace Erdos631

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

/-- A graph is planar if it can be embedded in the plane without edge crossings.
Mathlib does not yet have a formalization of graph planarity; we define it
here as an opaque predicate. -/
opaque IsPlanar {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop

/--
Erdős Problem 631, Part 1 (Thomassen's theorem [Th94]):

Every planar graph $G$ is 5-choosable, i.e., $\chi_L(G) \leq 5$.
-/
@[category research solved, AMS 5]
theorem erdos_631 : answer(True) ↔
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V), IsPlanar G → IsChoosable G 5 := by
  sorry

/--
Erdős Problem 631, Part 2 (Voigt's construction [Vo93]):

There exists a planar graph that is not 4-choosable, showing that 5 is best possible.
-/
@[category research solved, AMS 5]
theorem erdos_631.variants.tight : answer(True) ↔
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      IsPlanar G ∧ ¬IsChoosable G 4 := by
  sorry

end Erdos631
