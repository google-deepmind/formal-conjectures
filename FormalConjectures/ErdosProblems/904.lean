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

import FormalConjecturesUtil

/-!
# Erdős Problem 904

*References:*
- [erdosproblems.com/904](https://www.erdosproblems.com/904)
- [BoEr75] Bollobás, B. and Erdős, P., *Unsolved Problems*. Proc. Fifth British Combinatorial Conf. (1975), 678-680.
- [Er75] Erdős, P., *Some recent progress on extremal problems in graph theory*. Congr. Numer. (1975), 3-14.
- [Ed78] Edwards, C. S., *Complete subgraphs with largest sum of vertex degrees*. (1978), 293-306.
- [Fa92] Faudree, Ralph J., *Complete subgraphs with large degree sums*. J. Graph Theory (1992), 327-334.
- [BoNi05] Bollobás, Béla and Nikiforov, Vladimir, *The sum of degrees in cliques*. Electron. J. Combin. (2005), Note 21, 10.
-/

namespace Erdos904

open Finset

/-- An abbreviation for the fixed number of vertices $n$ in the graph. -/
abbrev n (V : Type*) [Fintype V] : ℕ := Fintype.card V

/-- The number of edges of the Turán graph $T(n, r)$, i.e. the Turán number. -/
abbrev turanNumber (n r : ℕ) : ℕ := #(SimpleGraph.turanGraph n r).edgeFinset

/--
Let $r\geq 2$ and let $t_r(n)$ be the Turán number (the maximal number of edges in a graph on $n$
vertices with no $K_{r+1}$).

If $G$ is a graph with $n$ vertices and $m\geq t_r(n)$ edges there exists a clique on $r$ vertices,
say $x_1,\ldots,x_r$, such that $$d(x_1)+\cdots+d(x_r)\geq \frac{2rm}{n}.$$

A conjecture of Bollobás and Erdős. This was conjectured in [Er75] only in the special case $r=3$. Edwards [Ed78] proved the conjecture for $2\leq r\leq 8$ (under the additional assumption that $n\geq r^2$). Faudree [Fa92] proved the conjecture for all $r\geq 2$ provided $n>\frac{r-1}{4}r^2$. The full conjecture was proved by Bollobás and Nikiforov [BoNi05].
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos904.lean"]
theorem erdos_904 :
    answer(True) ↔ ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (r : ℕ) (hr : r ∈ Set.Icc 1 (n V)) (hm : turanNumber (n V) r ≤ #G.edgeFinset),
      ∃ s, G.IsNClique r s ∧ 2 * r * #G.edgeFinset ≤ n V * ∑ v ∈ s, G.degree v := by
  sorry

end Erdos904
