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
# Erdős Problem 713

*Reference:* [erdosproblems.com/713](https://www.erdosproblems.com/713)

A problem of Erdős and Simonovits, worth \$500. See also Problem \#571.
-/

open SimpleGraph Filter

open scoped Topology

namespace Erdos713

/-- A graph $G$ contains $H$ as a subgraph via an injective graph homomorphism. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán extremal number $\operatorname{ex}(n; H)$: the maximum number of edges in a
simple graph on $n$ vertices that does not contain $H$ as a subgraph. -/
noncomputable def extremalNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph G H ∧ G.edgeSet.ncard = m}

/--
Erdős Problem 713, Part 1 (Erdős–Simonovits):

Is it true that for every finite bipartite graph $G$, there exist $\alpha \in [1, 2)$ and $c > 0$
such that $\operatorname{ex}(n; G) \sim cn^\alpha$, i.e.,
$\operatorname{ex}(n; G) / (cn^\alpha) \to 1$ as $n \to \infty$?
-/
@[category research open, AMS 5]
theorem erdos_713 : answer(sorry) ↔
    ∀ (U : Type) [Fintype U] (G : SimpleGraph U),
      G.Colorable 2 →
      ∃ α : ℝ, 1 ≤ α ∧ α < 2 ∧
      ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (extremalNumber G n : ℝ) / (c * (n : ℝ) ^ α))
        atTop (nhds 1) := by
  sorry

/--
Erdős Problem 713, Part 2 (Rationality of the exponent):

If $\operatorname{ex}(n; G) \sim cn^\alpha$ for a finite bipartite graph $G$, must $\alpha$ be
rational?
-/
@[category research open, AMS 5]
theorem erdos_713.variants.rationality : answer(sorry) ↔
    ∀ (U : Type) [Fintype U] (G : SimpleGraph U),
      G.Colorable 2 →
      ∀ α : ℝ, 1 ≤ α → α < 2 →
      ∀ c : ℝ, 0 < c →
      Tendsto (fun n : ℕ => (extremalNumber G n : ℝ) / (c * (n : ℝ) ^ α))
        atTop (nhds 1) →
      ∃ q : ℚ, (q : ℝ) = α := by
  sorry

end Erdos713
