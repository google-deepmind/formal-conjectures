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
# Erdős Problem 547

*References:*
- [erdosproblems.com/547](https://www.erdosproblems.com/547)
- [Bu74] Burr, S. A., Generalized Ramsey theory for graphs—a survey. Graphs and combinatorics
  (Proc. Capital Conf., George Washington Univ., Washington, D.C., 1973) (1974), 52-75.
- [Zh11] Zhao, Y., The Ramsey number of trees with large maximum degree. Random Structures
  Algorithms (2011), 324-340.
-/

namespace Erdos547

/--
If $T$ is a tree on $n$ vertices then
$$R(T) \leq 2n-2.$$
-/
@[category research open, AMS 5]
theorem erdos_547 :
    ∀ (n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n)),
      T.IsTree → SimpleGraph.diagonalGraphRamsey T ≤ 2 * n - 2 := by
  sorry

-- TODO: Add variants of the problem if they exist on the website.

end Erdos547
