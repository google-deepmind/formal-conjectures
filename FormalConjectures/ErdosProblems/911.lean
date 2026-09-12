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
# Erdős Problem 911

*Reference:* [erdosproblems.com/911](https://www.erdosproblems.com/911)
-/

open Filter SimpleGraph
open scoped Topology

namespace Erdos911

/-- The (diagonal) size Ramsey number $\hat{R}(G)$. -/
noncomputable def sizeRamseyHat {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sizeRamsey G G

/--
Let $\hat{R}(G)$ denote the size Ramsey number, the minimal number of edges $m$ such that there is
a graph $H$ with $m$ edges that is Ramsey for $G$.
Is there a function $f$ such that $f(x)/x\to \infty$ as $x\to \infty$ such that, for all large $C$,
if $G$ is a graph with $n$ vertices and $e\geq Cn$ edges then
$$
\hat{R}(G) > f(C) e?
$$
-/
@[category research open, AMS 5]
theorem erdos_911 :
    answer(sorry) ↔
      ∃ f : ℝ → ℝ, Tendsto (fun x : ℝ ↦ f x / x) atTop atTop ∧
        ∀ᶠ C : ℝ in atTop,
          ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
            C * n ≤ (G.edgeSet.ncard : ℝ) →
              f C * (G.edgeSet.ncard : ℝ) < sizeRamseyHat G := by
  sorry

end Erdos911
