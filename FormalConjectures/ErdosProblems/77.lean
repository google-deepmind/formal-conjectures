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
# Erdős Problem 77

*References:*
- [erdosproblems.com/77](https://www.erdosproblems.com/77)
- [Er47] Erdős, P., Some remarks on the theory of graphs. Bull. Amer. Math. Soc. (1947), 292-294.
-/

open scoped Topology

namespace Erdos77

/--
If $R(k)$ is the Ramsey number for $K_k$, the minimal $n$ such that every $2$-colouring of the edges
of $K_n$ contains a monochromatic copy of $K_k$, then find the value of
$$\lim_{k\to \infty}R(k)^{1/k}.$$
-/
@[category research open, AMS 5]
theorem erdos_77 :
    Filter.Tendsto (fun k : ℕ ↦ (SimpleGraph.diagonalRamsey k : ℝ) ^ (1 / (k : ℝ)))
      Filter.atTop (𝓝 answer(sorry)) := by
  sorry

/--
Erdős conjectured that the limit
$$\lim_{k\to \infty}R(k)^{1/k}$$
exists.
-/
@[category research open, AMS 5]
theorem erdos_77.parts.limit_exists :
    ∃ L : ℝ, Filter.Tendsto (fun k : ℕ ↦ (SimpleGraph.diagonalRamsey k : ℝ) ^ (1 / (k : ℝ)))
      Filter.atTop (𝓝 L) := by
  sorry

end Erdos77
