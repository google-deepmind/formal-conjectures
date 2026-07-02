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
# Erdős Problem 618

*References:*
- [erdosproblems.com/618](https://www.erdosproblems.com/618)
- [EGR98] Erdős, Paul and Gyárfás, András and Ruszinkó, Miklós, *How to decrease the diameter
  of triangle-free graphs*. Combinatorica (1998), 493-501.
-/

namespace Erdos618

open Filter Asymptotics

open scoped Classical in
/-- The maximum degree of a simple graph on `Fin n` (`0` when `n = 0`). -/
noncomputable def maxDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Finset.univ.sup fun v => G.degree v

open scoped Classical in
/-- For a graph `G` on `Fin n`, `h2 G` is the smallest number of edges that need to be added
to `G` so that the resulting supergraph has diameter at most `2` (every two distinct vertices
are adjacent or have a common neighbour) and is still triangle-free (`CliqueFree 3`).
By the `sInf` convention on `ℕ`, `h2 G = 0` if no such supergraph exists. -/
noncomputable def h2 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ H : SimpleGraph (Fin n),
    G ≤ H ∧
    H.CliqueFree 3 ∧
    (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
    (H.edgeFinset \ G.edgeFinset).card = k}

/--
For a triangle-free graph $G$ let $h_2(G)$ be the smallest number of edges that need to be
added to $G$ so that it has diameter $2$ and is still triangle-free. Is it true that if $G$
has maximum degree $o(n^{1/2})$ then $h(G)=o(n^2)$?

A problem of Erdős, Gyárfás, and Ruszinkó [EGR98]. Simonovits showed that there exist graphs
$G$ with maximum degree $\gg n^{1/2}$ and $h_2(G)\gg n^2$. Alon has observed this problem is
essentially identical to [134], and his solution in
[this note](https://web.math.princeton.edu/~nalon/PDFS/remark1901.pdf) also solves this
problem in the affirmative.

Formalization notes: $h(G)$ in the question is read as $h_2(G)$ (as in the problem's own
definition); "has diameter $2$" is read as diameter at most $2$ (the two coincide for
triangle-free graphs on at least $3$ vertices, since a complete graph is not triangle-free);
and the asymptotic hypothesis and conclusion are read along a family of triangle-free graphs
`G n` on `n` vertices, as in [134].
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos618.lean"]
theorem erdos_618 : answer(True) ↔
    ∀ (G : ∀ n : ℕ, SimpleGraph (Fin n)),
      (∀ n, (G n).CliqueFree 3) →
      (fun n => (maxDegree (G n) : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ ((1 : ℝ) / 2)) →
      (fun n => (h2 (G n) : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ 2) := by
  sorry

end Erdos618
