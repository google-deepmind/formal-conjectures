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
# Erdős Problem 1078

*Reference:* [erdosproblems.com/1078](https://www.erdosproblems.com/1078)
-/

open Filter SimpleGraph
open scoped Topology

namespace Erdos1078

/-- An $r$-partite graph with $n$ vertices in each part, on vertex set `Fin r × Fin n`. -/
def IsBalancedCompleteRPartite {r n : ℕ} (G : SimpleGraph (Fin r × Fin n)) : Prop :=
  ∀ a b : Fin r × Fin n, G.Adj a b → a.1 ≠ b.1

/--
Let $G$ be an $r$-partite graph with $n$ vertices in each part. If $G$ has minimum degree
$\geq (r-\frac{3}{2}-o(1))n$ then $G$ must contain a $K_r$.
-/
@[category research open, AMS 5]
theorem erdos_1078 :
    answer(sorry) ↔
      ∀ r ≥ 2, ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
        ∀ᶠ n : ℕ in atTop,
          ∀ (G : SimpleGraph (Fin r × Fin n)) [DecidableRel G.Adj],
            IsBalancedCompleteRPartite G →
              (r : ℝ) - 3 / 2 - o n ≤ (G.minDegree : ℝ) / n →
                (⊤ : SimpleGraph (Fin r)).IsContained G := by
  sorry

end Erdos1078
