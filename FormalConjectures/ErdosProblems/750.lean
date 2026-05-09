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
# Erdős Problem 750

*References:*
- [erdosproblems.com/750](https://www.erdosproblems.com/750)
- [Er94b] Erdős, Paul, _Some problems in number theory, combinatorics and combinatorial geometry_.
  Math. Pannon. (1994), 261-269.
-/

open Filter Finset NNReal

namespace Erdos750

/--
Let $f(m)$ be some function such that $f(m)\to \infty$ as $m\to \infty$. Does there exist a
graph $G$ of infinite chromatic number such that every subgraph on $m$ vertices contains
an independent set of size at least $\frac{m}{2}-f(m)$?

Note that in [Er94b] the function $f$ generalises a (proven) result for $f(m) = \epsilon m$,
where $\epsilon > 0$. Hence we should assume it is non-negative valued.
-/
@[category research open, AMS 5]
theorem erdos_750 :
    answer(sorry) ↔ ∀ (f : ℕ → ℝ≥0) (hf : atTop.Tendsto f atTop),
      ∃ (V : Type*) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ m / 2 - f m ≤ I.ncard := by
  sorry

end Erdos750
