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
# Erdős Problem 1013

Is it true that the ratio $h_3(k+1)/h_3(k)$ tends to 1, where $h_3(k)$ is the minimum number of
vertices of a triangle-free graph with chromatic number $k$?

*Reference:* [erdosproblems.com/1013](https://www.erdosproblems.com/1013)

[Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
-/

open SimpleGraph

namespace Erdos1013

/-- $h_3(k)$ is the minimum number of vertices $n$ such that there exists a
triangle-free graph on $n$ vertices with chromatic number exactly $k$. -/
noncomputable def h3 (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = (k : ℕ∞)}

/--
Erdős Problem 1013 [Er71]:

$$\lim_{k \to \infty} \frac{h_3(k+1)}{h_3(k)} = 1,$$

where $h_3(k)$ is the minimum number of vertices of a triangle-free graph with
chromatic number $k$.

Formulated as: for every $\varepsilon > 0$, there exists $K_0$ such that for all $k \geq K_0$,
$\left| \frac{h_3(k+1)}{h_3(k)} - 1 \right| \leq \varepsilon$.
-/
@[category research open, AMS 5]
theorem erdos_1013 :
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      |(h3 (k + 1) : ℝ) / (h3 k : ℝ) - 1| ≤ ε := by
  sorry

end Erdos1013
