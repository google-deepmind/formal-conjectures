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
Erdős and Gallai proved $f_3(n) = \lfloor (n-1)^2/4 \rfloor + 2$.

Simonovits [Er71] showed $f_r(n) = n^2/4 - g(r)/2 \cdot n + O(1)$, where $g(r)$ is
the largest $m$ such that any triangle-free graph with chromatic number $\geq r$
requires removing at least $m$ vertices to become bipartite.

The best known bounds on $g(r)$ are
$(1/2 - o(1)) r^2 \log r \leq g(r) \leq (2 + o(1)) r^2 \log r$.
The lower bound follows from Davies–Illingworth, and the upper bound from
Hefty–Horn–King–Pfender.

[Er71] Erdős, P., *On some extremal problems on $r$-graphs*, Discrete Mathematics 1 (1971), 1–6.
-/

open SimpleGraph Filter

namespace Erdos1011

/-- $f_r(n)$ is the minimum number of edges $m$ such that every graph on $n$ vertices
with at least $m$ edges and chromatic number $\geq r$ contains a triangle ($3$-clique). -/
noncomputable def minTriangleEdges (r n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n),
    G.edgeSet.ncard ≥ m → (r : ℕ∞) ≤ G.chromaticNumber → ¬G.CliqueFree 3}

/--
**Erdős Problem 1011** [Er71] — Simonovits asymptotic:

For every $r \geq 2$ there exist $g_r \in \mathbb{R}$ and $C \geq 0$ such that, for all
sufficiently large $n$,
$$|f_r(n) - (n^2 / 4 - g_r / 2 \cdot n)| \leq C.$$

Simonovits established this asymptotic form. The open problem is to determine
$g_r$ precisely; the best known bounds give $g_r \asymp r^2 \log r$.
-/
@[category research solved, AMS 5]
theorem erdos_1011 :
    ∀ r : ℕ, r ≥ 2 →
      ∃ (g_r : ℝ) (C : ℝ), 0 ≤ C ∧
        ∀ᶠ n in atTop,
          |(minTriangleEdges r n : ℝ) - ((n : ℝ) ^ 2 / 4 - g_r / 2 * (n : ℝ))| ≤ C := by
  sorry

end Erdos1011
