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
# Erdős Problem 151

*References:*
- [erdosproblems.com/151](https://www.erdosproblems.com/151)
- [Er88] Erdős, P., *Problems and results in combinatorial analysis and graph theory*.
  Discrete Math. (1988), 81-92.
- [EGT92] Erdős, P. and Gallai, T. and Tuza, Zs., *Covering the cliques of a graph with
  vertices*. Discrete Math. (1992), 279-289.
-/

@[expose] public section

namespace Erdos151

open SimpleGraph

variable {V : Type*}

/-- $H(n)$: the largest `k` such that every triangle-free graph on `n` vertices contains an
independent set on `k` vertices. -/
noncomputable def H (n : ℕ) : ℕ :=
  sSup {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}

/--
For a graph $G$, let $\tau(G)$ denote the minimal number of vertices that include at least one
from each maximal clique of $G$ on at least two vertices. Let $H(n)$ be maximal such that every
triangle-free graph on $n$ vertices contains an independent set on $H(n)$ vertices.

If $G$ is a graph on $n$ vertices, is $\tau(G)\leq n-H(n)$?

Erdős remarked that this is perhaps completely wrongheaded [Er88].
-/
@[category research open, question, AMS 5]
theorem erdos_151 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), cliqueTransversalNumber G ≤ n - H n := by
  sorry

/--
Erdős and Gallai made no progress on the question even when $G$ is $K_4$-free [Er88].
-/
@[category research open, question, AMS 5]
theorem erdos_151.variants.cliqueFree_four :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
      cliqueTransversalNumber G ≤ n - H n := by
  sorry

/--
If $G$ is triangle-free, then $\tau(G)\leq n-H(n)$: the complement of an independent set meets
every edge.
-/
@[category research solved, AMS 5]
theorem erdos_151.variants.cliqueFree_three (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : cliqueTransversalNumber G ≤ n - H n := by
  sorry

/--
It is easy to see that $\tau(G)\leq n-\sqrt{n}$. We state this with $\lfloor\sqrt{n}\rfloor$:
with the real square root the bound fails for a single edge ($n = 2$, $\tau = 1$).
-/
@[category research solved, AMS 5]
theorem erdos_151.variants.sqrt_bound (n : ℕ) (G : SimpleGraph (Fin n)) :
    cliqueTransversalNumber G ≤ n - Nat.sqrt n := by
  sorry

end Erdos151
