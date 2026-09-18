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
# Erdős Problem 927

*References:*
- [erdosproblems.com/927](https://www.erdosproblems.com/927)
- [MoMo65] Moon, J. W. and Moser, L., *On cliques in graphs*. Israel J. Math. (1965), 23-28.
- [Er66b] Erdős, P., *On cliques in graphs*. Israel J. Math. (1966), 233--234.
- [Er69b] Erdős, P., *Problems and results in chromatic graph theory*. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Sp71] Spencer, J. H., *On cliques in graphs*. Israel J. Math. (1971), 419-421.
-/

open Filter

namespace Erdos927

/-- `g n` is the maximum number of different sizes of cliques (maximal complete subgraphs) of a
graph on `n` vertices. -/
noncomputable def g (n : ℕ) : ℕ := by
  classical
  exact Finset.sup (Finset.univ (α := SimpleGraph (Fin n)))
    fun G => (SimpleGraph.cliqueSizes G).ncard

/--
Let $g(n)$ be the maximum number of different sizes of cliques that can occur in a graph on $n$
vertices. Estimate $g(n)$ - in particular, is it true that
$$g(n) = n - \log_2 n - \log_*(n) + O(1),$$
where $\log_*(n)$ is the number of iterated logarithms such that $\log \cdots \log n < 1$?

A quantity first considered by Moon and Moser [MoMo65], who proved
$n - \log_2 n - 2 \log \log n < g(n) \le n - \lfloor \log_2 n \rfloor$. Erdős [Er66b] improved the
lower bound to $n - \log_2 n - \log_*(n) - O(1) < g(n)$ and conjectured this was the correct order
of magnitude. This was disproved by Spencer [Sp71], who proved that in fact
$g(n) > n - \log_2 n - O(1)$.

Here $\log_2 n$ and $\log_*(n)$ are formalised as `Nat.log 2 n` and `Nat.iteratedLog 2 n`
(iterating `Nat.log 2` until the value is at most `1`); both differ from the quantities in the
problem by $O(1)$, so the statement is unaffected. See also `erdos_775.variants.spencer` and
`erdos_775.variants.moon_moser`.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos927.lean#L23"]
theorem erdos_927 : answer(False) ↔
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop,
      g n + Nat.log 2 n + Nat.iteratedLog 2 n ≤ n + C ∧
        n ≤ g n + Nat.log 2 n + Nat.iteratedLog 2 n + C := by
  sorry

end Erdos927
