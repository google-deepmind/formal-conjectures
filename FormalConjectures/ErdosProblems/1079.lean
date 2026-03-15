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
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

/-!
# Erdős Problem 1079

*Reference:* [erdosproblems.com/1079](https://www.erdosproblems.com/1079)

Let $r \geq 4$. If $G$ is a graph on $n$ vertices with at least $\operatorname{ex}(n; K_r)$ edges
then must $G$ contain a vertex with degree $d \gg_r n$ whose neighbourhood contains at least
$\operatorname{ex}(d; K_{r-1})$ edges?

As Erdős [Er75] says 'if true this would be a nice generalisation of Turán's theorem'.

This is true (unless $G$ is itself the Turán graph), proved by Bollobás and Thomason [BoTh81].
Bondy [Bo83b] showed that if $G$ has $> \operatorname{ex}(n; K_r)$ edges then the corresponding
vertex can be chosen to be of maximum degree in $G$.

[Er75] Erdős, P., _Some recent progress on extremal problems in graph theory_. Congressus
Numerantium (1975), 3–14.

[BoTh81] Bollobás, B., Thomason, A., _Dense neighbourhoods and Turán's theorem_. Journal of
Combinatorial Theory, Series B (1981), 111–114.

[Bo83b] Bondy, J. A., _Large dense neighbourhoods and Turán's theorem_. Journal of Combinatorial
Theory, Series B (1983), 109–111.
-/

open SimpleGraph Finset

namespace Erdos1079

/-- The number of edges of $G$ both of whose endpoints lie in a set $S$.
    Counts pairs $(i, j)$ in $S$ with $i < j$ and `G.Adj i j`. -/
noncomputable def neighborhoodEdgeCount {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/--
Erdős Problem 1079 [Er75]:

Let $r \geq 4$. If $G$ is a graph on $n$ vertices with at least $\operatorname{ex}(n; K_r)$ edges
then $G$ must contain a vertex $v$ with degree $d \gg_r n$ whose neighbourhood contains
at least $\operatorname{ex}(d; K_{r-1})$ edges.

Formalized as: for every $r \geq 4$, there exists $c > 0$ and $n_0$ such that for all
$n \geq n_0$ and all graphs $G$ on $n$ vertices with at least $\operatorname{ex}(n; K_r)$ edges,
there exists a vertex $v$ with degree $d \geq cn$ and at least
$\operatorname{ex}(d; K_{r-1})$ edges among the neighbors of $v$.

Proved by Bollobás and Thomason [BoTh81].
-/
@[category research solved, AMS 5]
theorem erdos_1079 : answer(True) ↔
    ∀ r : ℕ, r ≥ 4 →
    ∃ c : ℝ, c > 0 ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card ≥ extremalNumber n (⊤ : SimpleGraph (Fin r)) →
      ∃ v : Fin n,
        (G.degree v : ℝ) ≥ c * (n : ℝ) ∧
        neighborhoodEdgeCount G (G.neighborFinset v) ≥
          extremalNumber (G.degree v) (⊤ : SimpleGraph (Fin (r - 1))) := by
  sorry

/--
Bondy's strengthening of Erdős Problem 1079 [Bo83b]:

If $r \geq 4$ and $G$ is a graph on $n$ vertices with strictly more than
$\operatorname{ex}(n; K_r)$ edges, then a vertex of maximum degree in $G$ has at least
$\operatorname{ex}(d; K_{r-1})$ edges in its neighbourhood, where $d$ is that maximum degree.
-/
@[category research solved, AMS 5]
theorem erdos_1079_bondy_strengthening :
    ∀ r : ℕ, r ≥ 4 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card > extremalNumber n (⊤ : SimpleGraph (Fin r)) →
      ∀ v : Fin n, (∀ w : Fin n, G.degree w ≤ G.degree v) →
        neighborhoodEdgeCount G (G.neighborFinset v) ≥
          extremalNumber (G.degree v) (⊤ : SimpleGraph (Fin (r - 1))) := by
  sorry

end Erdos1079
