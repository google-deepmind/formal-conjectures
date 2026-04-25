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
# Zaremba's conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Zaremba%27s_conjecture)
-/

namespace ZarembaConjecture

/--
Zaremba's conjecture: there is an absolute constant $A$ such that for every denominator
$d > 1$, there is a numerator $a$ coprime to $d$, with $0 < a < d$, for which every partial
quotient in the continued fraction of $a/d$ is at most $A$.
-/
@[category research open, AMS 11]
theorem zaremba_conjecture :
    ∃ A : ℕ, 0 < A ∧ ∀ d : ℕ, 1 < d →
      ∃ a : ℕ, 0 < a ∧ a < d ∧ Nat.Coprime a d ∧
        ∀ n : ℕ, ∀ b : ℝ,
          (GenContFract.of ((a : ℝ) / (d : ℝ))).partDens.get? n = some b → b ≤ A := by
  sorry

end ZarembaConjecture
