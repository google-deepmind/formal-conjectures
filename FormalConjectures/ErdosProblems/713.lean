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
# Erdős Problem 713

*References:*
- [erdosproblems.com/713](https://www.erdosproblems.com/713)
- [Er67d] Erdős, P., *Some recent results on extremal problems in graph theory. {R}esults*. (1967),
  117--123 (English); pp. 124--130 (French).
- [ErSi70] Erdős, P. and Simonovits, M., *Some extremal problems in graph theory*. Combinatorial
  theory and its applications, I-III (Proc. Colloq., Balatonfüred, 1969) (1970), 377-390.
- [FrFu87] Frankl, P. and Füredi, Z., *Exact solution of some Turán-type problems*. J. Combin.
  Theory Ser. A (1987), 226--262.
- [FuGe21] Füredi, Zoltán and Gerbner, Dániel, *Hypergraphs without exponents*. J. Combin. Theory
  Ser. A (2021), Paper No. 105517, 9.
-/

open Filter SimpleGraph

namespace Erdos713

open scoped Classical in
/--
Is it true that, for every bipartite graph $G$, there exists some $\alpha\in [1,2)$ and $c>0$ such that $$\mathrm{ex}(n;G)\sim cn^\alpha?$$

The condition that $G$ have at least two edges excludes degenerate forbidden graphs whose
extremal number is eventually zero, for which the displayed asymptotic with $c>0$ is impossible.
-/
@[category research open, AMS 5]
theorem erdos_713.parts.i : answer(sorry) ↔
    ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
      ∃ α c : ℝ, α ∈ Set.Ico 1 2 ∧ 0 < c ∧
        Asymptotics.IsEquivalent atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => c * (n : ℝ) ^ α) := by
  sorry

open scoped Classical in
/--
Must $\alpha$ be rational?

The same nondegeneracy condition on $G$ is used as in part (i). Rationality means that the real
number $\alpha$ lies in the image of the canonical embedding $\mathbb{Q}\to\mathbb{R}$.
-/
@[category research open, AMS 5]
theorem erdos_713.parts.ii : answer(sorry) ↔
    ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
      ∀ α c : ℝ, α ∈ Set.Ico 1 2 → 0 < c →
        Asymptotics.IsEquivalent atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => c * (n : ℝ) ^ α) →
        α ∈ Set.range ((↑) : ℚ → ℝ) := by
  sorry

end Erdos713
