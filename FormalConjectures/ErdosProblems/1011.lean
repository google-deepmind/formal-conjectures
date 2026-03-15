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
# Erdős Problem 1011

*Reference:* [erdosproblems.com/1011](https://www.erdosproblems.com/1011)

Let $f_r(n)$ be minimal such that every graph on $n$ vertices with $\geq f_r(n)$
edges and chromatic number $\geq r$ contains a triangle. Determine $f_r(n)$.

Turán's theorem implies $f_2(n) = \lfloor n^2/4 \rfloor + 1$.
Erdős and Gallai [Er62d] proved $f_3(n) = \lfloor (n-1)^2/4 \rfloor + 2$.
Ren, Wang, Wang, and Yang [RWWY24] proved $f_4(n) = \lfloor (n-3)^2/4 \rfloor + 6$
for $n \geq 150$.

Simonovits [Si74] showed $f_r(n) = n^2/4 - g(r)/2 \cdot n + O(1)$, where $g(r)$ is
the largest $m$ such that any triangle-free graph with chromatic number $\geq r$
requires removing at least $m$ vertices to become bipartite.

The best known bounds on $g(r)$ are
$(1/2 - o(1)) r^2 \log r \leq g(r) \leq (2 + o(1)) r^2 \log r$.
The lower bound follows from Davies–Illingworth [DaIl22], and the upper bound from
Hefty–Horn–King–Pfender [HHKP25].

[Er62d] Erdős, P., _On a theorem of Rademacher-Turán_. Illinois J. Math. **6** (1962), 122–127.
[Si74] Simonovits, M., _Extremal graph problems with symmetrical extremal graphs.
Additional chromatic conditions_. Discrete Math. **7** (1974), 349–376.
[DaIl22] Davies, E., Illingworth, F., _The χ-Ramsey problem for triangle-free graphs_.
SIAM J. Discrete Math. (2022), 1124–1134.
[HHKP25] Hefty, L., Horn, P., King, R. and Pfender, F., _Improving R(3,k) in
just two bites_. arXiv:2510.19718 (2025).
[RWWY24] Ren, S., Wang, J., Wang, S. and Yang, W., _Extremal triangle-free graphs
with chromatic number at least four_. arXiv:2404.07486 (2024).
-/

open SimpleGraph Filter

namespace Erdos1011

/-- $f_r(n)$ is the minimum number of edges $m$ such that every graph on $n$ vertices
with at least $m$ edges and chromatic number $\geq r$ contains a triangle ($3$-clique). -/
noncomputable def minTriangleEdges (r n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n),
    G.edgeSet.ncard ≥ m → (r : ℕ∞) ≤ G.chromaticNumber → ¬G.CliqueFree 3}

/--
**Erdős Problem 1011** [Si74] — Simonovits asymptotic (solved):

For every $r \geq 2$ there exist $g_r \in \mathbb{R}$ and $C \geq 0$ such that, for all
sufficiently large $n$,
$$|f_r(n) - (n^2 / 4 - g_r / 2 \cdot n)| \leq C.$$

This formalizes the solved Simonovits asymptotic, not the full open problem of
determining $g_r$ precisely; the best known bounds give $g_r \asymp r^2 \log r$.
-/
@[category research solved, AMS 5]
theorem erdos_1011 :
    ∀ r : ℕ, r ≥ 2 →
      ∃ (g_r : ℝ) (C : ℝ), 0 ≤ C ∧
        ∀ᶠ n in atTop,
          |(minTriangleEdges r n : ℝ) - ((n : ℝ) ^ 2 / 4 - g_r / 2 * (n : ℝ))| ≤ C := by
  sorry

end Erdos1011
