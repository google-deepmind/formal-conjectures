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
# Erdős Problem 927

*Reference:* [erdosproblems.com/927](https://www.erdosproblems.com/927)

Let $g(n)$ be the maximum number of different sizes of cliques (maximal complete
subgraphs) that can occur in a graph on $n$ vertices. Is it true that
$$
  g(n) = n - \log_2 n - \log^*(n) + O(1),
$$
where $\log^*(n)$ is the iterated logarithm (the number of times the logarithm
must be applied before the result is less than $1$)?

DISPROVED by Spencer [Sp71], who proved that $g(n) > n - \log_2 n - O(1)$,
showing the $\log^*$ correction term is unnecessary.

See also [775].

[Sp71] Spencer, J., *The number of distinct clique sizes of a graph*.
-/

namespace Erdos927

/-- A set of vertices forms a clique (complete subgraph) in $G$ if every pair
    of distinct vertices in the set is adjacent. -/
def IsCliqueSet {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-- A maximal clique: a clique not properly contained in any other clique. -/
def IsMaxCliqueSet {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Prop :=
  IsCliqueSet G S ∧ ∀ T : Finset (Fin n), S ⊂ T → ¬IsCliqueSet G T

/-- The set of distinct sizes of maximal cliques in a simple graph. -/
def graphCliqueSizes {n : ℕ} (G : SimpleGraph (Fin n)) : Set ℕ :=
  {m : ℕ | ∃ S : Finset (Fin n), IsMaxCliqueSet G S ∧ S.card = m}

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

end Erdos927
