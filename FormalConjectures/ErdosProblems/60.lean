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
# Erdős Problem 60

*References:*
- [erdosproblems.com/60](https://www.erdosproblems.com/60)
- [HeMaYa21] He, J. and Ma, J. and Yang, T., *Some extremal results on 4-cycles*. Journal of
  Combinatorial Theory B (2021).
-/

namespace Erdos60

open SimpleGraph Filter
open scoped Real

/--
Does every graph on $n$ vertices with $>\mathrm{ex}(n;C_4)$ edges contain $\gg n^{1/2}$ many
copies of $C_4$?
-/
@[category research open, AMS 5]
theorem erdos_60 :
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (extremalNumber n (cycleGraph 4) < G.edgeFinset.card) →
          (c * Real.sqrt (n : ℝ) ≤ ({ H' : G.Subgraph | Nonempty (H'.coe ≃g cycleGraph 4) }.ncard : ℝ)) := by
  sorry

end Erdos60
