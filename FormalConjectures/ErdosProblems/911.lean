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
# Erdős Problem 911

*References:*
- [erdosproblems.com/911](https://www.erdosproblems.com/911)
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*.
  (1982), 59--79.
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos911

/--
Let $\hat{R}(G)$ denote the size Ramsey number, the minimal number of edges $m$ such that there is
a graph $H$ with $m$ edges that is Ramsey for $G$.

Is there a function $f$ such that $f(x)/x\to \infty$ as $x\to \infty$ such that, for all large $C$,
if $G$ is a graph with $n$ vertices and $e\geq Cn$ edges then
$$\hat{R}(G) > f(C) e?$$

Here $\hat{R}(G)$ is `sizeRamsey G G`, and $G$ has at least one vertex (for $n = 0$ the
inequality fails trivially).
-/
@[category research open, question, AMS 5]
theorem erdos_911 :
    ∃ f : ℝ → ℝ, Tendsto (fun x ↦ f x / x) atTop atTop ∧
      ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
        C * n ≤ (G.edgeSet.ncard : ℝ) →
          f C * G.edgeSet.ncard < (sizeRamsey G G : ℝ) := by
  sorry

end Erdos911
