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
# Erdős Problem 146

Erdős and Simonovits conjectured that the Turán number of any $r$-degenerate bipartite
graph $H$ satisfies $\text{ex}(n; H) = O(n^{2 - 1/r})$.

*Reference:* [erdosproblems.com/146](https://www.erdosproblems.com/146)

[ErSi84] Erdős, P. and Simonovits, M., *Cube-supersaturated graphs and related
problems*, Progress in graph theory (Waterloo, Ont., 1982), Academic Press,
Toronto, ON, 1984, 203-218.

[AKS03] Alon, N., Krivelevich, M., and Sudakov, B., *Turán numbers of bipartite
graphs and related Ramsey-type questions*, Combinatorics, Probability and
Computing 12 (2003), no. 5-6, 477-494.
-/

open SimpleGraph

namespace Erdos146

/-- An injective graph homomorphism from $H$ to $F$; witnesses that $F$ contains a
subgraph isomorphic to $H$. -/
def ContainsSubgraph {V U : Type*} (F : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → F.Adj (f u) (f v)

/-- The Turán number $\text{ex}(n; H)$: the maximum number of edges in a simple graph on $n$
vertices that contains no copy of $H$ as a subgraph. -/
noncomputable def turanNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬ContainsSubgraph F H ∧ F.edgeFinset.card = m}

/-- A graph $G$ is $r$-degenerate if every non-empty finite set of vertices contains
a vertex with at most $r$ neighbors within that set. Equivalently, every induced
subgraph of $G$ has minimum degree at most $r$. -/
def IsRDegenerateGraph {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ (S : Set V), S.Finite → S.Nonempty →
    ∃ v ∈ S, (G.neighborSet v ∩ S).ncard ≤ r

/--
Erdős-Simonovits Conjecture (Problem #146) [ErSi84]:
If $H$ is a bipartite graph that is $r$-degenerate (i.e., every induced subgraph of $H$
has minimum degree at most $r$), then
$$\text{ex}(n; H) \ll n^{2 - 1/r}.$$
That is, there exists a constant $C > 0$ such that $\text{ex}(n; H) \leq C \cdot n^{2 - 1/r}$
for all $n \geq 1$.

This is open even for $r = 2$. Alon, Krivelevich, and Sudakov [AKS03] proved the
weaker bound $\text{ex}(n; H) \ll n^{2 - 1/(4r)}$.
-/
@[category research open, AMS 5]
theorem erdos_146 :
    ∀ (r : ℕ), 1 ≤ r →
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
      Nonempty (H.Coloring (Fin 2)) →
      IsRDegenerateGraph H r →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (turanNumber H n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) := by
  sorry

end Erdos146
