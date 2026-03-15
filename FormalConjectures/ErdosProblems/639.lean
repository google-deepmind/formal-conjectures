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
# Erdős Problem 639

Erdős conjectured that in any 2-coloring of the edges of $K_n$, at most $\lfloor n^2/4 \rfloor$
edges do not lie in a monochromatic triangle. This was solved by Erdős, Rousseau, and Schelp
for large $n$ (unpublished). Alon observed that the conjecture also follows from a result of
Pyber [Py86], who showed that at most $\lfloor n^2/4 \rfloor + 2$ monochromatic cliques cover
all edges of a 2-coloured $K_n$ for sufficiently large $n$. Keevash and Sudakov [KeSu04]
completely solved the problem, establishing the exact threshold for all $n$: the answer is
$\binom{n}{2}$ for $n \leq 5$, $10$ for $n = 6$, and $\lfloor n^2/4 \rfloor$ for $n \geq 7$.

*Reference:* [erdosproblems.com/639](https://www.erdosproblems.com/639)

[Er97d] Erdős, P., _Some of my favourite problems in various branches of combinatorics_,
Matematiche (Catania), 1997.

[Py86] Pyber, L., _Clique covering of graphs_, Combinatorica **6** (1986), 393–398.

[KeSu04] Keevash, P. and Sudakov, B., _On the number of edges not covered by monochromatic
copies of a fixed graph_, J. Combin. Theory Ser. B **90** (2004), 41–53.
-/

namespace Erdos639

/-- A 2-coloring of the edges of the complete graph on $\operatorname{Fin} n$.
Represented as a symmetric function assigning a color ($\operatorname{Bool}$) to each pair
of distinct vertices. -/
structure EdgeTwoColoring (n : ℕ) where
  color : Fin n → Fin n → Bool
  symm : ∀ u v : Fin n, color u v = color v u

/-- An edge $\{u, v\}$ lies in a monochromatic triangle under coloring $c$ if there
exists a vertex $w$ distinct from both $u$ and $v$ such that all three edges
$\{u,v\}$, $\{u,w\}$, $\{v,w\}$ have the same color. -/
def EdgeTwoColoring.inMonoTriangle {n : ℕ} (c : EdgeTwoColoring n)
    (u v : Fin n) : Prop :=
  ∃ w : Fin n, w ≠ u ∧ w ≠ v ∧
    c.color u v = c.color u w ∧ c.color u v = c.color v w

/-- The number of edges of $K_n$ (counted as unordered pairs with $u < v$) that
do not lie in any monochromatic triangle under coloring $c$. -/
noncomputable def edgesNotInMonoTriangleCount {n : ℕ} (c : EdgeTwoColoring n) : ℕ :=
  Set.ncard {p : Fin n × Fin n | p.1 < p.2 ∧ ¬c.inMonoTriangle p.1 p.2}

/--
Erdős Problem 639 [Er97d]:
If the edges of $K_n$ are 2-coloured then there are at most $\lfloor n^2/4 \rfloor$ edges
which do not occur in a monochromatic triangle.

Solved by Keevash and Sudakov [KeSu04], who proved the threshold is exactly
$\lfloor n^2/4 \rfloor$ for all $n \geq 7$.
-/
@[category research solved, AMS 5]
theorem erdos_639 (n : ℕ) (hn : 7 ≤ n) (c : EdgeTwoColoring n) :
    edgesNotInMonoTriangleCount c ≤ n ^ 2 / 4 := by
  sorry

end Erdos639
