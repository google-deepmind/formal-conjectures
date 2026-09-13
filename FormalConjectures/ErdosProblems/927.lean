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

*Reference:* [erdosproblems.com/927](https://www.erdosproblems.com/927)
-/

open Filter SimpleGraph Real
open scoped Topology

namespace Erdos927

/-- The number of distinct clique sizes occurring in `G`. -/
noncomputable def cliqueSizeSet {V : Type*} [Fintype V] (G : SimpleGraph V) : Set ℕ :=
  { k | ∃ s : Finset V, G.IsNClique k s }

/-- $g(n)$ is the maximum number of different sizes of cliques in an $n$-vertex graph. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup { (cliqueSizeSet G).ncard | (G : SimpleGraph (Fin n)) }

/-- Number of iterated logarithms until the value drops below 1. -/
noncomputable def iteratedLog (n : ℕ) : ℕ :=
  sInf { k | (fun x : ℝ ↦ log x)^[k] n < 1 }

/--
Let $g(n)$ be the maximum number of different sizes of cliques that can occur in a graph on $n$
vertices. Estimate $g(n)$ - in particular, is it true that
$$
g(n)=n-\log_2n-\log_*(n)+O(1),
$$
where $\log_*(n)$ is the number of iterated logarithms such that $\log\cdots \log n <1$.
-/
@[category research open, AMS 5]
theorem erdos_927 :
    answer(sorry) ↔
      ∃ C : ℝ, ∀ n ≥ 2,
        |(g n : ℝ) - (n - logb 2 n - iteratedLog n)| ≤ C := by
  sorry

end Erdos927
