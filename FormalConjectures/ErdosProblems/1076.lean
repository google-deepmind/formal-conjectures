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
# Erdős Problem 1076

*References:*
- [erdosproblems.com/1076](https://www.erdosproblems.com/1076)
- [BES73] Brown, W. G., Erdős, P. and Sós, V. T., *Some extremal problems on $r$-graphs*.
  (1973), 53-63.
- [BoWa19] Bohman, T. and Warnke, L., *Large girth approximate Steiner triple systems*.
  J. Lond. Math. Soc. (2) (2019), 895-913.
- [Er74c] Erdős, P., *Extremal problems on graphs and hypergraphs*. (1974), 75-84.
- [GKLO20] Glock, S., Kühn, D., Lo, A. and Osthus, D., *On a conjecture of Erdős on locally
  sparse Steiner triple systems*. Combinatorica (2020), 363-403.
- [Gl19] Glock, S., *Triple systems with no three triples spanning at most five points*.
  Bull. Lond. Math. Soc. (2019), 230-236.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1076

/--
$\mathrm{ex}_3(n,\mathcal{F}_k)$, where $\mathcal{F}_k$ is the family of all $3$-uniform
hypergraphs with $k$ vertices and $k-2$ edges: the maximum number of edges of a $3$-uniform
hypergraph on $n$ vertices in which no $k$ vertices span at least $k-2$ edges.
-/
noncomputable abbrev ex (n k : ℕ) : ℕ :=
  Hypergraph.configurationExtremalNumber n 3 k (k - 2)

/--
The maximum number of edges of a $3$-uniform hypergraph on $n$ vertices that contains no
hypergraph with $j$ vertices and $j-2$ edges for any $4\leq j\leq k$.
-/
noncomputable abbrev exUpTo (n k : ℕ) : ℕ :=
  Hypergraph.extremalNumber n 3 fun H ↦ ∀ j ∈ Finset.Icc 4 k, ¬ H.ContainsSubgraph j (j - 2)

/--
Let $k\geq 5$ and let $\mathcal{F}_k$ be the family of all $3$-uniform hypergraphs with $k$
vertices and $k-2$ edges. Is it true that
$$\mathrm{ex}_3(n,\mathcal{F}_k)\sim \frac{n^2}{6}?$$

A question of Brown, Erdős, and Sós [BES73]. For the single family $\mathcal{F}_k$ stated here
the answer is no: Glock [Gl19] proved that $\mathrm{ex}_3(n,\mathcal{F}_5)\sim \frac{n^2}{5}$,
see `erdos_1076.variants.five`.

The asymptotic $\frac{n^2}{6}$ holds when all of $\mathcal{F}_4,\ldots,\mathcal{F}_k$ are
forbidden together, see `erdos_1076.variants.up_to`.
-/
@[category research solved, question, AMS 5]
theorem erdos_1076 :
    ¬ ∀ k ≥ 5, (fun n : ℕ ↦ (ex n k : ℝ)) ~[atTop] fun n ↦ (n : ℝ) ^ 2 / 6 := by
  sorry

/--
Glock [Gl19] proved that the maximum number of edges of a $3$-uniform hypergraph on $n$ vertices
in which no three edges span at most five vertices is $(1+o(1))\frac{n^2}{5}$.
-/
@[category research solved, AMS 5]
theorem erdos_1076.variants.five :
    (fun n : ℕ ↦ (ex n 5 : ℝ)) ~[atTop] fun n ↦ (n : ℝ) ^ 2 / 5 := by
  sorry

/--
Brown, Erdős, and Sós [BES73] proved that $\mathrm{ex}_3(n,\mathcal{F}_4)\sim \frac{n^2}{6}$.
-/
@[category research solved, AMS 5]
theorem erdos_1076.variants.four :
    (fun n : ℕ ↦ (ex n 4 : ℝ)) ~[atTop] fun n ↦ (n : ℝ) ^ 2 / 6 := by
  sorry

/--
Let $k\geq 5$. The maximum number of edges of a $3$-uniform hypergraph on $n$ vertices that
contains no hypergraph with $j$ vertices and $j-2$ edges for any $4\leq j\leq k$ is
$(1+o(1))\frac{n^2}{6}$.

This was proved independently by Bohman and Warnke [BoWa19] and Glock, Kühn, Lo, and Osthus
[GKLO20]. It is the approximate version of Erdős Problem 207.
-/
@[category research solved, AMS 5]
theorem erdos_1076.variants.up_to :
    ∀ k ≥ 5, (fun n : ℕ ↦ (exUpTo n k : ℝ)) ~[atTop] fun n ↦ (n : ℝ) ^ 2 / 6 := by
  sorry

end Erdos1076
