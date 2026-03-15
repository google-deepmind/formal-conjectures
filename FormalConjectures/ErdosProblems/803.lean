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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Balanced

/-!
# Erdős Problem 803

*Reference:* [erdosproblems.com/803](https://www.erdosproblems.com/803)

*Related:* [Erdős Problem 1077](https://www.erdosproblems.com/1077)

We call a graph $H$ *$D$-balanced* (or *$D$-almost-regular*) if the maximum
degree of $H$ is at most $D$ times the minimum degree of $H$.

A problem of Erdős and Simonovits [ErSi70]. Disproved by Alon [Al08], who
showed that for every $D > 1$ and large $n$ there is a graph $G$ with $n$
vertices and $\geq n \log n$ edges such that every $D$-balanced subgraph on $m$
vertices has $\ll m \sqrt{\log m} + \log D$ edges.

Janzer and Sudakov [JaSu23] proved a partial positive result: any graph on $n$
vertices with $\geq n \log n$ edges contains an $O(1)$-balanced subgraph on
$m \geq k$ vertices with $\gg_k \sqrt{\log m} / (\log \log m)^{3/2} \cdot m$
edges.

[ErSi70] Erdős, P. and Simonovits, M., _Some extremal problems in graph
theory_. Combinatorial theory and its applications, I–III (Proc. Colloq.,
Balatonfüred, 1969) (1970), 377–390.

[Al08] Alon, N., _Problems and results in extremal combinatorics. II_.
Discrete Mathematics (2008), 4460–4472.

[JaSu23] Janzer, O. and Sudakov, B., _Resolution of the Erdős–Sauer problem
on regular subgraphs_. Forum Mathematics Pi (2023), Paper No. e19, 13 pages.
-/

open SimpleGraph Classical

namespace Erdos803

/--
Erdős Problem 803 [ErSi70] (Disproved by Alon [Al08]):

Is it true that there exist absolute constants $D \geq 1$ and $C > 0$ such that
for every $m \geq 1$, there exists $N_0$ such that for all $n \geq N_0$, every
graph on $n$ vertices with at least $n \cdot \log(n)$ edges contains a
$D$-balanced subgraph on $m$ vertices with at least $C \cdot m \cdot \log(m)$
edges?
-/
@[category research solved, AMS 5]
theorem erdos_803 :
    answer(False) ↔
    ∃ D : ℕ, D ≥ 1 ∧ ∃ C : ℝ, C > 0 ∧
    ∀ m : ℕ, m ≥ 1 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ (G : SimpleGraph (Fin n)),
      (G.edgeFinset.card : ℝ) ≥ (n : ℝ) * Real.log (n : ℝ) →
      ∃ (H : SimpleGraph (Fin m)) (f : Fin m → Fin n),
        Function.Injective f ∧
        (∀ u v, H.Adj u v → G.Adj (f u) (f v)) ∧
        H.IsBalanced (D : ℝ) ∧
        (H.edgeFinset.card : ℝ) ≥ C * (m : ℝ) * Real.log (m : ℝ) := by
  sorry

end Erdos803
