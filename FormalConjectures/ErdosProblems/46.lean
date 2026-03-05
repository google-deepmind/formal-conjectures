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
# Erdős Problem 46

*Reference:* [erdosproblems.com/46](https://www.erdosproblems.com/46)

For every finite colouring of the integers $\geq 2$, there exists a monochromatic finite
set whose reciprocals sum to $1$. Proved by Croot [Cr03].

[Cr03] Croot, E.S., _On a coloring conjecture about unit fractions_, Annals of Mathematics **157** (2003), 545–556.
-/

open Finset BigOperators

namespace Erdos46

/--
For every finite colouring of the positive integers $\ge 2$, there exists a
monochromatic finite set $\{n_1, \ldots, n_k\}$ with $2 \le n_1 < \cdots < n_k$ whose
reciprocals sum to $1$, i.e. $\sum 1/n_i = 1$.

Proved by Croot [Cr03].
-/
@[category research solved, AMS 5 11]
theorem erdos_46 : answer(True) ↔
    ∀ (α : Type*) [Finite α] (c : ℕ → α),
      ∃ S : Finset ℕ, S.Nonempty ∧
        (∀ n ∈ S, n ≥ 2) ∧
        (∃ color : α, ∀ n ∈ S, c n = color) ∧
        (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1 := by
  sorry

end Erdos46
