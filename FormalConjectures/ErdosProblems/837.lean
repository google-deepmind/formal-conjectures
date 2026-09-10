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
# Erdős Problem 837

*References:*
- [erdosproblems.com/837](https://www.erdosproblems.com/837)
-/

namespace Erdos837

open Filter Asymptotics

/--
Let $k\geq 2$ and $A_k\subseteq [0,1]$ be the set of $\alpha$ such that there exists some
$\beta(\alpha)>\alpha$ with the property that, if $G_1,G_2,\ldots$ is a sequence of $k$-uniform
hypergraphs with
$$\liminf \frac{e(G_n)}{\binom{\lvert G_n\rvert}{k}} >\alpha$$
then there exist subgraphs $H_n\subseteq G_n$ such that $\lvert H_n\rvert \to \infty$ and
$$\liminf \frac{e(H_n)}{\binom{\lvert H_n\rvert}{k}} >\beta,$$
and further that this property does not necessarily hold if $>\alpha$ is replaced by $\geq \alpha$.
What is $A_3$?
-/
@[category research open, AMS 5]
theorem erdos_837 :
    {α : ℝ | α ∈ Set.Icc 0 1 ∧ ∃ β : ℝ, α < β ∧
    Hypergraph.HasDensityJump 3 α β true ∧ ¬ Hypergraph.HasDensityJump 3 α β false}
      = answer(sorry) := by
  sorry

end Erdos837
