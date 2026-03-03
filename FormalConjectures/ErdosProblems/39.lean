/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 39

*Reference:* [erdosproblems.com/39](https://www.erdosproblems.com/39)
-/

namespace Erdos39

open Filter

/--
Is there an infinite Sidon set $A\subset \mathbb{N}$ such that
$\lvert A\cap \{1\ldots,N\}\rvert \gg_\epsilon N^{1/2-\epsilon}$
for all $\varepsilon > 0$?
-/
@[category research open, AMS 11]
theorem erdos_39 : answer(sorry) ↔ ∃ (A : Set ℕ), A.Infinite ∧ IsSidon A ∧
    ∀ᵉ  (ε  > (0 : ℝ)),
    (· ^ (1 / 2 - ε) : ℕ → ℝ) =O[atTop] fun N => (((Set.Icc 1 N) ∩ A).ncard : ℝ) := by
  sorry

-- TODO(firsching): add the various known bounds as variants.

/--
It is known that every Sidon set $A \subseteq \{1,\ldots,N\}$ satisfies $|A| \leq N^{1/2} + O(N^{1/4})$
(Erdős–Turán 1941). Constructions using algebraic geometry over finite fields (e.g., Singer 1938)
give infinite Sidon sets with $|A \cap \{1,\ldots,N\}| \gg N^{1/2 - o(1)}$, nearly matching the conjecture.
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/39", AMS 11]
theorem erdos_39.variants.known_result :
    ∃ (A : Set ℕ), A.Infinite ∧ IsSidon A ∧
      (fun N : ℕ => Real.sqrt N / Real.log N) =O[atTop]
        fun N => (((Set.Icc 1 N) ∩ A).ncard : ℝ) := by
  sorry

end Erdos39
