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
# Erdős Problem 712

*References:*
- [erdosproblems.com/712](https://www.erdosproblems.com/712)
- [Er81] Erdős, P., On the combinatorial problems which I would most like to see solved.
  Combinatorica (1981), 25-42.
-/

namespace Erdos712

open Filter Asymptotics
open scoped Topology

/--
Determine, for any $k>r>2$, the limiting value as $n\to\infty$ of
$$\frac{\mathrm{ex}_r(n,K_k^r)}{\binom{n}{r}},$$
where $\mathrm{ex}_r(n,K_k^r)$ is the largest number of $r$-edges which can placed on $n$ vertices
so that there exists no set of $k$ vertices which is covered by all $\binom{k}{r}$ possible
$r$-edges.
-/
@[category research open, AMS 5]
theorem erdos_712 :
    let L : ℕ → ℕ → ℝ := answer(sorry)
    ∀ k r : ℕ, 2 < r → r < k →
      Tendsto (fun n ↦ (Hypergraph.cliqueExtremalNumber n r k : ℝ) / n.choose r)
        atTop (𝓝 (L k r)) := by
  sorry

end Erdos712
