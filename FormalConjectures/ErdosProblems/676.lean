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
# Erdős Problem 676

*References:*
- [erdosproblems.com/676](https://www.erdosproblems.com/676)
- [Er79] Erdős, Paul, *Some unconventional problems in number theory*.
  Math. Mag. (1979), 67–70.
- [Er79d] Erdős, P., *Some unconventional problems in number theory*.
  Acta Math. Acad. Sci. Hungar. (1979), 71–80.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*.
  Ann. Discrete Math. (1980), 89–115.
-/

namespace Erdos676

open Filter

/-- Is every sufficiently large integer of the form $ap^2+b$ for some prime $p$ and integers
$a \geq 1$ and $0 \leq b < p$? -/
@[category research open, AMS 11]
theorem erdos_676 : answer(sorry) ↔ ∀ᶠ n in atTop,
    ∃ a p b : ℕ, p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b := by
  sorry

/- TODO: Formalize the source's additional variants: the quantitative almost-all result, the
version without primality, the general pair $(A,f)$, and the questions about the minimal $c_n$. -/

end Erdos676
