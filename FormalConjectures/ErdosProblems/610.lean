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
# Erdős Problem 610

*References:*
- [erdosproblems.com/610](https://www.erdosproblems.com/610)
- [EGT92] Erdős, Paul and Gallai, Tibor and Tuza, Zsolt, *Covering the cliques of a graph with
  vertices*. Discrete Math. (1992), 279-289.
- [JMRS21] Joret, Gwenaël and Micek, Piotr and Reed, Bruce and Smid, Michiel, *Tight bounds on
  the clique chromatic number*. Electron. J. Combin. (2021), Paper No. 3.51, 8.
  [arXiv:2006.11353](https://arxiv.org/abs/2006.11353)
- [Ki95] Kim, J. H., *The Ramsey number $R(3,t)$ has order of magnitude $t^2/\log t$*.
  Random Structures and Algorithms (1995), 173-207.
-/

@[expose] public section

open Filter Real SimpleGraph

namespace Erdos610

/--
For a graph $G$ let $\tau(G)$ denote the minimal number of vertices that include at least one
from each maximal clique of $G$ (aside from isolated vertices). This is sometimes called the
clique transversal number.

Estimate $\tau(G)$. In particular, is it true that if $G$ has $n$ vertices then
$$\tau(G) \leq n-\omega(n)\sqrt{n}$$
for some $\omega(n)\to\infty$?

The stronger inequality in part ii follows from the results of Joret, Micek, Reed, and Smid
[JMRS21]. The function $\omega$ and the threshold are uniform over all graphs.
-/
@[category research solved, AMS 5]
theorem erdos_610.parts.i : answer(True) ↔
    ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), (G.cliqueTransversalNum : ℝ) ≤ n - ω n * √n := by
  sorry

/--
Is it true that if $G$ has $n$ vertices then
$$\tau(G) \leq n-c\sqrt{n\log n}$$
for some absolute constant $c>0$?

The inequality follows from the results of Joret, Micek, Reed, and Smid [JMRS21], who prove
that if $G$ is a graph on $n$ vertices then there exists a $k$-colouring of the vertices, for
some $k\ll (n/\log n)^{1/2}$, such that every maximal clique (aside from isolated vertices)
contains at least two colours. The bound on $\tau(G)$ follows from taking the union of all
except the largest colour class.

The bound is formalised for every sufficiently large $n$, uniformly over all graphs.
-/
@[category research solved, AMS 5]
theorem erdos_610.parts.ii : answer(True) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (G.cliqueTransversalNum : ℝ) ≤ n - c * √((n : ℝ) * log n) := by
  sorry

/--
A problem of Erdős, Gallai, and Tuza [EGT92], who proved that
$$\tau(G) \leq n-\sqrt{2n}+O(1).$$
-/
@[category research solved, AMS 5]
theorem erdos_610.variants.erdos_gallai_tuza :
    ∃ C : ℝ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (G.cliqueTransversalNum : ℝ) ≤ n - √(2 * (n : ℝ)) + C := by
  sorry

/--
The bound in part ii would be best possible, since there exist triangle-free graphs with all
independent sets of size $O(\sqrt{n\log n})$, which follows from the lower bound for $R(3,k)$
by Kim [Ki95]. Thus, for some $C>0$, there are graphs on every sufficiently large number $n$
of vertices with $\tau(G) \geq n-C\sqrt{n\log n}$.
-/
@[category research solved, AMS 5]
theorem erdos_610.variants.lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      (n : ℝ) - C * √((n : ℝ) * log n) ≤ G.cliqueTransversalNum := by
  sorry

end Erdos610
