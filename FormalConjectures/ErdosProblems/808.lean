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
# Erdős Problem 808

*Reference:* [erdosproblems.com/808](https://www.erdosproblems.com/808)

Erdős conjectured that for any set $A \subset \mathbb{N}$ with $|A| = n$ and any graph $G$ on $A$
with at least $n^{1+c}$ edges, the graph-restricted sumset or product set must satisfy
$\max(|A +_G A|, |A \cdot_G A|) \geq n^{1+c-\varepsilon}$. This strengthens Problem #52
(the Erdős–Szemerédi sum-product conjecture). Disproved by Alon, Ruzsa, and Solymosi [ARS20].

[Er77c] Erdős, P., _Problems and results on combinatorial number theory. III._. Number Theory Day
(Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72.

[ErSz83] Erdős, P. and Szemerédi, E., _On sums and products of integers_. Studies in Pure
Mathematics, Birkhäuser, Basel (1983), 213–218.

[Er91] Erdős, P., _Problems and results in combinatorial number theory_.

[Er97] Erdős, P., _Some of my new and almost new problems and results in combinatorial
number theory_ (1997).

[ARS20] Alon, N., Ruzsa, I., and Solymosi, J., _Sums, products, and ratios along the edges of a
graph_. Publ. Mat. (2020), 143–155.
-/

open SimpleGraph Finset

namespace Erdos808

/-- The graph-restricted sumset $\{f(i) + f(j) : (i, j) \in E(G)\}$. -/
def graphSumset {n : ℕ} (f : Fin n → ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Finset ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).image
    (fun p => f p.1 + f p.2)

/-- The graph-restricted product set $\{f(i) \cdot f(j) : (i, j) \in E(G)\}$. -/
def graphProdset {n : ℕ} (f : Fin n → ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Finset ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).image
    (fun p => f p.1 * f p.2)

/--
Erdős Problem 808 (disproved) [Er77c], [ErSz83], [Er91], [Er97]:

For all $c, \varepsilon > 0$, for sufficiently large $n$, if $A \subset \mathbb{N}$ has
$|A| = n$ and $G$ is any graph on $A$ with at least $n^{1+c}$ edges then
$$
\max(|A +_G A|, |A \cdot_G A|) \geq n^{1+c-\varepsilon}.
$$

Disproved by Alon, Ruzsa, and Solymosi [ARS20].
-/
@[category research solved, AMS 5 11]
theorem erdos_808 : ¬
    (∀ (c ε : ℝ), 0 < c → 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ (f : Fin n → ℕ), Function.Injective f →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (n : ℝ) ^ (1 + c) ≤ (G.edgeFinset.card : ℝ) →
    (n : ℝ) ^ (1 + c - ε) ≤
      max ((graphSumset f G).card : ℝ) ((graphProdset f G).card : ℝ)) := by
  sorry

end Erdos808
