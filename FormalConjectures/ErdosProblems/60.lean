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

/- ## Variants and partial results -/

/--
He, Ma, and Yang [HeMaYa21] proved the conjecture when $n = q^2 + q + 1$ for some even integer $q$.
-/
@[category research solved, AMS 5]
theorem erdos_60.variants.he_ma_yang :
    ∃ c : ℝ, c > 0 ∧
      ∀ (q : ℕ) (_hq : Even q),
        ∀ (G : SimpleGraph (Fin (q^2 + q + 1))) [DecidableRel G.Adj],
          (extremalNumber (q^2 + q + 1) (cycleGraph 4) < G.edgeFinset.card) →
          (c * Real.sqrt ((q^2 + q + 1) : ℝ) ≤ ({ H' : G.Subgraph | Nonempty (H'.coe ≃g cycleGraph 4) }.ncard : ℝ)) := by
  sorry

/--
Erdős and Simonovits conjectured that at least 2 copies of $C_4$ are guaranteed.
-/
@[category research solved, AMS 5]
theorem erdos_60.variants.two_copies :
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (extremalNumber n (cycleGraph 4) < G.edgeFinset.card) →
        (2 ≤ { H' : G.Subgraph | Nonempty (H'.coe ≃g cycleGraph 4) }.ncard) := by
  sorry

end Erdos60
