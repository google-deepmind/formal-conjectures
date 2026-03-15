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
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Erdős Problem 163

*Reference:* [erdosproblems.com/163](https://www.erdosproblems.com/163)

The Burr-Erdős conjecture: For any $d \geq 1$, if $H$ is a graph on $n$ vertices such
that every subgraph of $H$ contains a vertex of degree at most $d$ (i.e., $H$ is
$d$-degenerate), then $R(H) \leq C_d \cdot n$ for some constant $C_d$ depending only on $d$.

Proved by Lee [Le17], who showed $R(H) \leq 2^{2^{O(d)}} \cdot n$.

[BuEr75] Burr, S. A. and Erdős, P., _On the magnitude of generalized Ramsey numbers for graphs_.
Infinite and finite sets, Vol. 1 (1975), 214–240.

[Er82e] Erdős, P., _Problems and results on finite and infinite graphs_. Recent advances
in graph theory (Proc. Second Czechoslovak Sympos., Prague, 1982).

[Le17] Lee, C., _Ramsey numbers of degenerate graphs_. Ann. of Math. **186** (2017), 791–829.

See also Problem 800, which is a special case of this conjecture.
-/

open SimpleGraph Finset

namespace Erdos163

/-- A simple graph $H$ on a finite vertex type is $d$-degenerate if every nonempty
    subset $S$ of vertices contains a vertex $v$ with at most $d$ neighbours in $S$. -/
def IsDDegenerate {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (d : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty →
    ∃ v ∈ S, (S.filter (H.Adj v)).card ≤ d

/-- The diagonal Ramsey number $R(H)$: the minimum $N$ such that for every simple
    graph $G$ on $\operatorname{Fin} N$, either $G$ or $G^c$ contains a copy of $H$. -/
noncomputable def ramseyDiag {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    H.IsContained G ∨ H.IsContained Gᶜ}

/--
Erdős Problem 163 [BuEr75, Er82e] — The Burr-Erdős Conjecture:

For every $d \geq 1$, there exists a constant $C_d > 0$ such that for every
$d$-degenerate graph $H$ on $n$ vertices, $R(H, H) \leq C_d \cdot n$.

Equivalently, if $H$ is the union of $c$ forests then $R(H) \leq C_c \cdot n$.

Proved by Lee [Le17], who showed $R(H) \leq 2^{2^{O(d)}} \cdot n$.
-/
@[category research solved, AMS 5]
theorem erdos_163 :
    ∀ d : ℕ, 1 ≤ d →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    IsDDegenerate H d →
      (ramseyDiag H : ℝ) ≤ C * (n : ℝ) := by
  sorry

end Erdos163
