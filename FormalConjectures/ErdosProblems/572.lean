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
# Erdős Problem 572

*References:*
- [erdosproblems.com/572](https://www.erdosproblems.com/572)
- [Er64c] Erdős, P., Extremal problems in graph theory. Theory of Graphs and its
  Applications (1964), 29-36.
- [BoSi74] Bondy, J. A. and Simonovits, M., Cycles of even length in graphs.
  J. Combin. Theory Ser. B (1974), 97-105.
- [LUW95] Lazebnik, F., Ustimenko, V. A. and Woldar, A. J., A new series of dense graphs
  of high girth. Bull. Amer. Math. Soc. (N.S.) (1995), 73-79.
-/

open Filter

namespace Erdos572

/--
Show that for $k\geq 3$
$$\mathrm{ex}(n;C_{2k})\gg n^{1+\frac{1}{k}}.$$

Erdős [Er64c] and Bondy and Simonovits [BoSi74] proved the upper bound $O(k n^{1+1/k})$.
This problem is #46 in Extremal Graph Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_572 (k : ℕ) (hk : 3 ≤ k) :
    ∃ c > (0 : ℝ), ∀ᶠ (n : ℕ) in atTop,
      c * (n : ℝ) ^ (1 + 1 / (k : ℝ)) ≤
        (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * k)) : ℝ) := by
  sorry

-- TODO: Add variants of the problem.

end Erdos572
