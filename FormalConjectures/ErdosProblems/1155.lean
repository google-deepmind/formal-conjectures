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
# Erdős Problem 1155

*Reference:* [erdosproblems.com/1155](https://www.erdosproblems.com/1155)

Construct a random graph on $n$ vertices in the following way: begin with the complete graph
$K_n$. At each stage, choose uniformly a random triangle in the graph and delete all the edges
of this triangle. Repeat until the graph is triangle-free. If $f(n)$ is the number of edges
remaining, is it true that $\mathbb{E}[f(n)] \asymp n^{3/2}$ and that $f(n) \ll n^{3/2}$
almost surely?

A problem of Bollobás and Erdős [Bo98, p.231][Va99, 3.61].

Bohman, Frieze, and Lubetzky [BFL15] proved that $f(n) = n^{3/2 + o(1)}$ a.s.

[Bo98] Bollobás, B., _Modern Graph Theory_, Graduate Texts in Mathematics 184, Springer (1998).

[Va99] Vu, V. H. (1999), 3.61.

[Gr97] Grable, D. A., _On random greedy triangle packing_, Electronic Journal of
Combinatorics 4 (1997), Research Paper 11.

[BFL15] Bohman, T., Frieze, A., and Lubetzky, E., _Random triangle removal_,
Advances in Mathematics 280 (2015), 379--438.
-/

open SimpleGraph Filter

open scoped Topology

namespace Erdos1155

/-- The triangle removal process on $K_n$: starting from the complete graph on $n$
    vertices, repeatedly choose a uniformly random triangle and remove all three
    of its edges, until the graph is triangle-free.

    `triangleRemovalExpectedEdges n` is $\mathbb{E}[f(n)]$, the expected number of edges
    remaining when the process terminates. -/
opaque triangleRemovalExpectedEdges (n : ℕ) : ℝ

/-- The probability that the number of edges remaining after the triangle
    removal process on $K_n$ satisfies a given predicate $P$. -/
opaque triangleRemovalEdgeProb (n : ℕ) (P : ℕ → Prop) : ℝ

/--
Erdős Problem #1155, Part 1 [Bo98, p.231]:

$\mathbb{E}[f(n)] \asymp n^{3/2}$, i.e., there exist constants $c_1, c_2 > 0$ such that for all
sufficiently large $n$, $c_1 \cdot n^{3/2} \leq \mathbb{E}[f(n)] \leq c_2 \cdot n^{3/2}$.
-/
@[category research open, AMS 5 60]
theorem erdos_1155 : answer(sorry) ↔
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        c₁ * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ triangleRemovalExpectedEdges n ∧
        triangleRemovalExpectedEdges n ≤ c₂ * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  sorry

/--
Erdős Problem #1155, Part 2 [Bo98, p.231]:

$f(n) \ll n^{3/2}$ almost surely, i.e., there exists $C > 0$ such that with
probability tending to $1$, $f(n) \leq C \cdot n^{3/2}$.
-/
@[category research open, AMS 5 60]
theorem erdos_1155.variants.almost_sure : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun n : ℕ =>
        triangleRemovalEdgeProb n (fun k => (k : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2)))
        atTop (nhds 1) := by
  sorry

/--
Erdős Problem #1155, Variant (Bohman–Frieze–Lubetzky [BFL15]):

$f(n) = n^{3/2 + o(1)}$ almost surely, i.e., for every $\varepsilon > 0$, the probability that
$n^{3/2 - \varepsilon} \leq f(n) \leq n^{3/2 + \varepsilon}$ tends to $1$ as $n \to \infty$.
This strengthens Part 2 by providing a matching almost-sure lower bound.
-/
@[category research solved, AMS 5 60]
theorem erdos_1155.variants.bfl15 : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ =>
        triangleRemovalEdgeProb n (fun k =>
          (n : ℝ) ^ ((3 : ℝ) / 2 - ε) ≤ (k : ℝ) ∧
          (k : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2 + ε)))
        atTop (nhds 1) := by
  sorry

end Erdos1155
