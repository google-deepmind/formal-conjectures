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
# Erdős Problem 1178

*Reference:* [erdosproblems.com/1178](https://www.erdosproblems.com/1178)

For $r, e \geq 3$, determine the minimal $d$ such that the $r$-uniform Turán number
$\operatorname{ex}_r(n; d, e) = o(n^2)$ as $n \to \infty$. The conjecture is that this
minimal $d$ equals $(r-2) \cdot e + 3$.

[BES73] Brown, W. G., Erdős, P., and Sós, V. T., *On the existence of triangulated spheres
in 3-graphs, and related problems*, 1973.

[Er75b] Erdős, P., *Problems and results on finite and infinite combinatorial analysis*, 1975.

[Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*, 1981.
-/

open Filter Asymptotics

namespace Erdos1178

/-- An $r$-uniform hypergraph on vertex type $V$ is a set of $r$-element subsets of $V$. -/
def IsRUniform (r : ℕ) {V : Type*} (E : Finset (Finset V)) : Prop :=
  ∀ e ∈ E, e.card = r

/-- An $r$-uniform hypergraph on $n$ vertices contains a sub-hypergraph on $d$ vertices
with $e$ edges: there exist $d$ vertices in $\operatorname{Fin} n$ such that the hypergraph has
at least $e$ $r$-uniform edges entirely within those $d$ vertices. Since $F_r(d,e)$
contains all $r$-uniform hypergraphs on $d$ vertices with $e$ edges, avoiding $F$ means
no $d$ vertices span $e$ or more $r$-uniform edges. -/
def ContainsConfig (d e n : ℕ) (E : Finset (Finset (Fin n))) : Prop :=
  ∃ S : Finset (Fin n), S.card = d ∧ e ≤ (E.filter (fun edge => edge ⊆ S)).card

/-- The $r$-uniform Turán number $\operatorname{ex}_r(n; d, e)$: the maximum number of edges in an
$r$-uniform hypergraph on $n$ vertices that contains no $r$-uniform sub-hypergraph
on $d$ vertices with $e$ edges (i.e., avoids the Brown-Erdős-Sós family $F_r(d,e)$). -/
noncomputable def turanNumber (r n d e : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ E : Finset (Finset (Fin n)),
    IsRUniform r E ∧ ¬ ContainsConfig d e n E ∧ E.card = m}

/-- The minimal $d$ such that the $r$-uniform Turán number
$\operatorname{ex}_r(n; d, e) = o(n^2)$ as $n \to \infty$. -/
noncomputable def minD (r e : ℕ) : ℕ :=
  sInf {d : ℕ | (fun n : ℕ => (turanNumber r n d e : ℝ)) =o[atTop]
                (fun n : ℕ => (n : ℝ) ^ 2)}

/--
Erdős Problem 1178 [BES73] [Er75b] [Er81]:

For $r, e \geq 3$, the minimal $d$ such that the $r$-uniform Turán number
$\operatorname{ex}_r(n, F) = o(n^2)$ (where $F$ is the family of all $r$-uniform hypergraphs
on $d$ vertices with $e$ edges) equals $(r-2) \cdot e + 3$.

Here `turanNumber r n d e` is the maximum number of edges in an $r$-uniform hypergraph
on $n$ vertices avoiding all configurations on $d$ vertices with $e$ edges: formally, there
is no $d$-element set $S \subseteq \operatorname{Fin} n$ with $e$ or more $r$-uniform edges
in $S$. `minD r e` is the least such $d$.

Brown, Erdős, and Sós proved the lower bound $d_r(e) \geq (r-2) \cdot e + 3$.
Erdős, Frankl, and Rödl proved the case $e = 3$: $d_r(3) = 3(r-2)+3$ for all $r \geq 3$.
-/
@[category research open, AMS 5]
theorem erdos_1178 (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e) :
    minD r e = (r - 2) * e + 3 := by
  sorry

end Erdos1178
