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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1033

*References:*
- [erdosproblems.com/1033](https://www.erdosproblems.com/1033)
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*. (1982),
  59--79.
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [ErLa85] Erdős, Paul and Laskar, Renu, *A note on the size of a chordal subgraph*.
  Congr. Numer. (1985), 81--86.
- [Fa88] Fan, Genghua, *Degree sum for a triangle in a graph*. J. Graph Theory (1988), 249--263.
-/

@[expose] public section

open Filter Finset

namespace Erdos1033

/--
Let $h(n)$ be such that every graph on $n$ vertices with $>n^2/4$ many edges contains a triangle
whose vertices have degrees summing to at least $h(n)$. Estimate $h(n)$. In particular, is it
true that
$$h(n)\geq (2(\sqrt{3}-1)-o(1))n?$$

A conjecture of Bollobás and Erdős.

The answer is no. A blow-up of the butterfly graph, posted on the
[Erdős problems forum](https://www.erdosproblems.com/forum/thread/1033) in June and July 2026 and
written up in [this note](https://woutercvb.github.io/Erdos1033_smalloptimization.pdf), gives
arbitrarily large graphs with more than $n^2/4$ edges in which every triangle has degree sum at
most $1.464n$, which is less than $2(\sqrt{3}-1)n$. Estimating the optimal value of $h(n)$ is
still open.
-/
@[category research solved, AMS 5]
theorem erdos_1033 : answer(False) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      n ^ 2 < 4 * #G.edgeFinset →
        ∃ t, G.IsNClique 3 t ∧
          (2 * (Real.sqrt 3 - 1) - ε) * n ≤ ∑ v ∈ t, (G.degree v : ℝ) := by
  sorry

/--
In [Er82e] it is asked whether $h(n)\geq \frac{3}{2}n$. The answer is no, since the construction
of Erdős and Laskar [ErLa85] gives $h(n) \leq 2(\sqrt{3}-1)n+O(1)$ and
$2(\sqrt{3}-1) < \frac{3}{2}$.
-/
@[category research solved, AMS 5]
theorem erdos_1033.variants.three_halves : answer(False) ↔
    ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], n ^ 2 < 4 * #G.edgeFinset →
      ∃ t, G.IsNClique 3 t ∧ 3 * n ≤ 2 * ∑ v ∈ t, G.degree v := by
  sorry

/--
Fan [Fa88] proved that $h(n) \geq \frac{21}{16}n$: every graph on $n$ vertices with $>n^2/4$
edges contains a triangle whose degrees sum to at least $\frac{21}{16}n$.
-/
@[category research solved, AMS 5]
theorem erdos_1033.variants.fan (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : n ^ 2 < 4 * #G.edgeFinset) :
    ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v := by
  sorry

open scoped Classical in
/--
Erdős and Laskar [ErLa85] gave a construction showing that $h(n) \leq 2(\sqrt{3}-1)n+O(1)$:
for all large $n$ there is a graph on $n$ vertices with $>n^2/4$ edges in which every triangle
has degree sum at most $2(\sqrt{3}-1)n+O(1)$. The construction is made explicit in [Fa88].
-/
@[category research solved, AMS 5]
theorem erdos_1033.variants.erdos_laskar :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n), n ^ 2 < 4 * #G.edgeFinset ∧
      ∀ t, G.IsNClique 3 t → ∑ v ∈ t, (G.degree v : ℝ) ≤ 2 * (Real.sqrt 3 - 1) * n + C := by
  sorry

end Erdos1033
