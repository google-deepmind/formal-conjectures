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
# Erdős Problem 1014

See also problems [544](https://www.erdosproblems.com/544) and
[1030](https://www.erdosproblems.com/1030).

*References:*
- [erdosproblems.com/1014](https://www.erdosproblems.com/1014)
- [Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109.
-/

open Filter SimpleGraph

open scoped Topology

namespace Erdos1014

/--
Erdős Problem 1014 [Er71, p.99]:

For fixed $k \geq 3$,
$$\lim_{l \to \infty} R(k, l+1) / R(k, l) = 1,$$
where $R(k, l)$ is the Ramsey number.
-/
@[category research open, AMS 5]
theorem erdos_1014 (k : ℕ) (hk : k ≥ 3) :
    Tendsto (fun l : ℕ =>
      (graphRamseyNumber k (l + 1) : ℝ) / (graphRamseyNumber k l : ℝ))
      atTop (nhds 1) := by
  sorry

/--
The $k = 3$ case of Erdős Problem 1014 [Er71]:

$$\lim_{l \to \infty} R(3, l+1) / R(3, l) = 1.$$

This is already open.
-/
@[category research open, AMS 5]
theorem erdos_1014.variants.k_eq_3 :
    Tendsto (fun l : ℕ =>
      (graphRamseyNumber 3 (l + 1) : ℝ) / (graphRamseyNumber 3 l : ℝ))
      atTop (nhds 1) := by
  sorry

/--
The $k = 2$ case of Erdős Problem 1014: $R(2, l+1) / R(2, l) \to 1$, since
$R(2, l) = l$ for all $l$.
-/
@[category undergraduate, AMS 5]
theorem erdos_1014.variants.k_eq_2 :
    Tendsto (fun l : ℕ =>
      (graphRamseyNumber 2 (l + 1) : ℝ) / (graphRamseyNumber 2 l : ℝ))
      atTop (nhds 1) := by
  sorry

end Erdos1014
