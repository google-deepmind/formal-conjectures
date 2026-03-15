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
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 927

*Reference:* [erdosproblems.com/927](https://www.erdosproblems.com/927)

Let $g(n)$ be the maximum number of different sizes of cliques (maximal complete
subgraphs) that can occur in a graph on $n$ vertices. Is it true that
$$
  g(n) = n - \log_2 n - \log^*(n) + O(1),
$$
where $\log^*(n)$ is the iterated logarithm (the number of times the logarithm
must be applied before the result is less than $1$)?

Moon and Moser [MoMo65] first studied $g(n)$ and proved
$n - \log_2 n - 2\log\log n < g(n) \leq n - \lfloor \log_2 n \rfloor$.
Erdős [Er66b] improved the lower bound to $g(n) > n - \log_2 n - \log^*(n) - O(1)$
and conjectured this was the correct order of magnitude.

DISPROVED by Spencer [Sp71], who proved that $g(n) > n - \log_2 n - O(1)$,
showing the $\log^*$ correction term is unnecessary.

See also [775].

[Er66b] Erdős, P., _On cliques in graphs_. Israel Journal of Mathematics (1966), 233–234.

[Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof Techniques in Graph
Theory (1969), 27-35.

[Er71] Erdős, P., _Topics in combinatorial analysis_. Proc. Second Louisiana Conf. on
Combinatorics, Graph Theory and Computing (1971), 2–20.

[MoMo65] Moon, J. W. and Moser, L., _On cliques in graphs_. Israel Journal of Mathematics
(1965), 23–28.

[Sp71] Spencer, J. H., _The number of distinct clique sizes of a graph_. Israel Journal of
Mathematics (1971), 419–421.
-/

open SimpleGraph

namespace Erdos927

/-- The set of distinct sizes of maximal cliques in a simple graph on `n` vertices. -/
def graphCliqueSizes {n : ℕ} (G : SimpleGraph (Fin n)) : Set ℕ :=
  {m : ℕ | ∃ S : Finset (Fin n), Maximal (fun T : Finset (Fin n) => G.IsClique ↑T) S ∧
    S.card = m}

/--
Erdős Problem 927 (DISPROVED by Spencer [Sp71]):

Is it true that $g(n) = n - \log_2 n - \log^*(n) + O(1)$?

The right-hand side formalizes a necessary consequence of the conjecture: since
$\log^*(n) \to \infty$, the conjecture implies that for every constant $C$,
$g(n) \leq n - \lfloor \log_2 n \rfloor - C$ for all sufficiently large $n$.
Spencer showed $g(n) \geq n - \lfloor \log_2 n \rfloor - O(1)$, disproving this.
-/
@[category research solved, AMS 5]
theorem erdos_927 : answer(False) ↔
    (∀ C : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ G : SimpleGraph (Fin n),
        (graphCliqueSizes G).ncard + Nat.log 2 n + C ≤ n) := by
  sorry

/--
Spencer's lower bound [Sp71]: there exists a constant $C$ such that for every $n$,
some graph on $n$ vertices has at least $n - \lfloor \log_2 n \rfloor - C$ distinct
maximal clique sizes.
-/
@[category research solved, AMS 5]
theorem erdos_927.variants.spencer_lower_bound :
    ∃ C : ℕ, ∀ n : ℕ, ∃ G : SimpleGraph (Fin n),
      (graphCliqueSizes G).ncard + C ≥ n - Nat.log 2 n := by
  sorry

/--
Moon–Moser upper bound [MoMo65]: $g(n) \leq n - \lfloor \log_2 n \rfloor$, i.e.,
every graph on $n$ vertices has at most $n - \lfloor \log_2 n \rfloor$ distinct
maximal clique sizes.
-/
@[category research solved, AMS 5]
theorem erdos_927.variants.moon_moser_upper_bound :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (graphCliqueSizes G).ncard ≤ n - Nat.log 2 n := by
  sorry

end Erdos927
