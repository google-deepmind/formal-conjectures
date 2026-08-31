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
# Erdős Problem 571

*References:*
- [erdosproblems.com/571](https://www.erdosproblems.com/571)
-/

open Filter SimpleGraph

namespace Erdos571

/--
Show that for any rational $\alpha \in [1,2)$ there exists a bipartite graph $G$ such that $$\mathrm{ex}(n;G)\asymp n^{\alpha}.$$
-/
@[category research open, AMS 5]
theorem erdos_571 :
    ∀ α : ℚ, 1 ≤ α → α < 2 →
      ∃ q : ℕ, ∃ G : SimpleGraph (Fin q), G.IsBipartite ∧
        Asymptotics.IsTheta atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => (n : ℝ) ^ (α : ℝ)) := by
  sorry

end Erdos571
