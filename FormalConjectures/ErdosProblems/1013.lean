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

Related problems: #920 (generalization to $K_r$-free graphs), #1104 (dual formulation).

OEIS: [A292528](https://oeis.org/A292528).

*Reference:* [erdosproblems.com/1013](https://www.erdosproblems.com/1013)

[Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.

[GrYa68] Graver, J., Yackel, J., _Some graph theoretic results associated with Ramsey's theorem_.
Journal of Combinatorial Theory (1968), 125–175.
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

Note: this would follow from the known asymptotic bounds
$(1/2 - o(1))k^2 \log k \leq h_3(k) \leq (1 + o(1))k^2 \log k$ (see Problem 1104).
-/
@[category research open, AMS 5]
theorem erdos_1013 :
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      |(h3 (k + 1) : ℝ) / (h3 k : ℝ) - 1| ≤ ε := by
  sorry

end Erdos1013
