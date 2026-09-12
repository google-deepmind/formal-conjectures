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
# Erdős Problem 625

*References:*
- [erdosproblems.com/625](https://www.erdosproblems.com/625)
- [ErGi93] Erdős, P. and Gimbel, J., *Choose independence or a clique*. J. Graph Theory (1993).
-/

open Filter SimpleGraph

open scoped Classical Topology

namespace Erdos625

/-- Uniform probability of a property of $G(n,1/2)$, i.e. of a uniform random graph on `n`
vertices. -/
noncomputable def prob (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  ({G : SimpleGraph (Fin n) | P G}.ncard : ℝ) / (2 : ℝ) ^ n.choose 2

/--
It is known that almost surely
$$\frac{n}{2\log_2 n} \leq \zeta(G) \leq \chi(G) \leq \frac{n}{2\log_2 n}(1 + o(1)).$$
-/
@[category research solved, AMS 5 60]
theorem erdos_625.variants.sandwich :
    ∀ ε > (0 : ℝ), Tendsto (fun n : ℕ =>
      prob n fun G =>
        (n : ℝ) / (2 * Real.logb 2 n) ≤ G.cochromaticNumber.toReal ∧
          G.cochromaticNumber ≤ G.chromaticNumber ∧
          G.chromaticNumber.toReal ≤
            (n : ℝ) / (2 * Real.logb 2 n) * (1 + ε)) atTop (nhds 1) := by
  sorry

/--
Almost surely, $\chi(G)-\zeta(G)\to\infty$ as $n\to\infty$ for $G=G(n,1/2)$.
-/
@[category research open, AMS 5 60]
theorem erdos_625 : answer(sorry) ↔
    ∀ k : ℕ, Tendsto (fun n : ℕ =>
      prob n fun G => (k : ℕ∞) ≤ G.chromaticNumber - G.cochromaticNumber) atTop (nhds 1) := by
  sorry

end Erdos625
