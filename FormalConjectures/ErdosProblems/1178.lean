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

[BES73] Brown, W.G., Erdős, P., and Sós, V.T., *Some extremal problems on r-graphs*.
1973, pp. 53–63.

[Er75b] Erdős, P., *Problems and results in combinatorial number theory*. Journées
Arithmétiques de Bordeaux (1974), 1975, pp. 295–310.

[RuSz78] Ruzsa, I.Z. and Szemerédi, E., *Triple systems with no six points carrying
three triangles*. Combinatorics (Proc. Fifth Hungarian Colloq., Keszthely, 1976),
Vol. II, Colloq. Math. Soc. János Bolyai 18, North-Holland, 1978, pp. 939–945.

[EFR86] Erdős, P., Frankl, P., Rödl, V., *The asymptotic number of graphs not containing
a fixed subgraph and a problem for hypergraphs having no exponent*. Graphs and
Combinatorics (1986), pp. 113–121.
-/

open Filter Asymptotics

namespace Erdos1178

/-- An $r$-uniform hypergraph on vertex type $V$ is a set of $r$-element subsets of $V$. -/
def IsRUniform (r : ℕ) {V : Type*} (E : Finset (Finset V)) : Prop :=
  ∀ e ∈ E, e.card = r

/-- There exist $d$ vertices spanning at least $e$ edges from $E$. -/
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

Brown, Erdős, and Sós [BES73] proved the lower bound $d_r(e) \geq (r-2) \cdot e + 3$.
Ruzsa and Szemerédi [RuSz78] proved $d_3(3) = 6$.
Erdős, Frankl, and Rödl [EFR86] proved the case $e = 3$: $d_r(3) = 3(r-2)+3$ for all $r \geq 3$.
-/
@[category research open, AMS 5]
theorem erdos_1178 (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e) :
    minD r e = (r - 2) * e + 3 := by
  sorry

end Erdos1178
