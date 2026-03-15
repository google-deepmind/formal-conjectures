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
# Erdős Problem 113

*Reference:* [erdosproblems.com/113](https://www.erdosproblems.com/113)

Erdős–Simonovits conjecture (disproved by Janzer): is it true that for a bipartite graph $G$,
the Turán number satisfies $\mathrm{ex}(n; G) \ll n^{3/2}$ if and only if $G$ is 2-degenerate?

[ErSi84] Erdős, P. and Simonovits, M., *Cube-supersaturated graphs and related problems*,
Progress in graph theory (Waterloo, Ont., 1982), Academic Press, Toronto, ON, 1984, 203–218.

[Er93] Erdős, P., *Some of my favorite solved and unsolved problems in graph theory*.
Quaestiones Mathematicae **16** (1993), 333–350.

[Ja23b] Janzer, O., *Disproof of a conjecture of Erdős and Simonovits on the Turán number
of graphs with minimum degree 3*. International Mathematics Research Notices (2023), 8478–8494.
-/

open SimpleGraph

namespace Erdos113

/-- An injective graph homomorphism from $H$ to $F$; witnesses that $F$ contains a
subgraph isomorphic to $H$. -/
def ContainsSubgraph {V U : Type*} (F : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → F.Adj (f u) (f v)

/-- The Turán number $\operatorname{ex}(n; H)$: the maximum number of edges in a simple graph
on $n$ vertices that contains no copy of $H$ as a subgraph. -/
noncomputable def turanNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬ContainsSubgraph F H ∧ F.edgeFinset.card = m}

/-- A graph $G$ is 2-degenerate if every non-empty finite set of vertices contains
a vertex with at most 2 neighbors within that set. Equivalently, $G$ has no
induced subgraph with minimum degree at least 3. -/
def IsTwoDegenerateGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (S : Set V), S.Finite → S.Nonempty →
    ∃ v ∈ S, (G.neighborSet v ∩ S).ncard ≤ 2

/--
Erdős–Simonovits Conjecture (Problem #113) [ErSi84]:
For a bipartite graph $G$ on a finite vertex set, the Turán number satisfies
$$
  \operatorname{ex}(n; G) \ll n^{3/2}
$$
if and only if $G$ is 2-degenerate (i.e., $G$ has no induced subgraph with minimum
degree at least 3).

Here $\operatorname{ex}(n; G) \ll n^{3/2}$ means there exists a constant $C > 0$ such that
$\operatorname{ex}(n; G) \leq C \cdot n^{3/2}$ for all $n$.

DISPROVED by Janzer [Ja23b]: for any $\varepsilon > 0$, there exists a 3-regular bipartite
graph $H$ such that $\operatorname{ex}(n; H) \ll n^{4/3 + \varepsilon}$. Since a 3-regular graph is not
2-degenerate but its Turán number is still $o(n^{3/2})$, the "only if" direction
($\operatorname{ex}(n; G) \ll n^{3/2} \to G$ is 2-degenerate) fails.
-/
@[category research solved, AMS 5]
theorem erdos_113 : answer(False) ↔
    ∀ (U : Type*) (G : SimpleGraph U) [Fintype U] [DecidableRel G.Adj],
      Nonempty (G.Coloring (Fin 2)) →
      (IsTwoDegenerateGraph G ↔
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
          (turanNumber G n : ℝ) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ)) := by
  sorry

end Erdos113
