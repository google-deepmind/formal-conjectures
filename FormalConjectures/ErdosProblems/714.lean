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
# Erdős Problem 714

Is it true that $\operatorname{ex}(n; K_{r,r}) \gg n^{2-1/r}$ for all $r \geq 2$?

*Reference:* [erdosproblems.com/714](https://www.erdosproblems.com/714)
-/

open SimpleGraph

namespace Erdos714

/-- A graph $G$ contains $H$ as a subgraph via an injective graph homomorphism. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán extremal number $\operatorname{ex}(n; H)$: the maximum number of edges in a
simple graph on $n$ vertices that does not contain $H$ as a subgraph. -/
noncomputable def extremalNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph G H ∧ G.edgeSet.ncard = m}

/--
Erdős Problem 714:

For every $r \geq 2$, the extremal number $\operatorname{ex}(n; K_{r,r})$ satisfies a lower bound
of order $n^{2-1/r}$. That is, there exist $C > 0$ and $N_0$ such that for all
$n \geq N_0$:
$$\operatorname{ex}(n; K_{r,r}) \geq C \cdot n^{2-1/r}.$$

Here $K_{r,r}$ is represented by `completeBipartiteGraph (Fin r) (Fin r)` from
Mathlib, the complete bipartite graph on `Fin r ⊕ Fin r`.

Kövári, Sós, and Turán proved the matching upper bound
$\operatorname{ex}(n; K_{r,r}) \ll n^{2-1/r}$ for all $r \geq 2$. The conjecture asks whether
the lower bound of the same order also holds.

The conjectured lower bound is known for $r = 2$ and $r = 3$.
-/
@[category research open, AMS 5]
theorem erdos_714 : answer(sorry) ↔
    ∀ r : ℕ, 2 ≤ r →
      ∃ C : ℝ, 0 < C ∧
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
          C * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
            (extremalNumber (completeBipartiteGraph (Fin r) (Fin r)) n : ℝ) := by
  sorry

end Erdos714
