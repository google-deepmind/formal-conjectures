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
# Erdős Problem 46

*References:*
- [erdosproblems.com/46](https://www.erdosproblems.com/46)
- [Cr03] Croot, III, Ernest S., *On a coloring conjecture about unit fractions*. Ann. of Math. (2)
  (2003), 545-556.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos46

/--
Does every finite colouring of the integers have a monochromatic solution to
$1=\sum \frac{1}{n_i}$ with $2\leq n_1<\cdots <n_k$?

The answer is yes, as proved by Croot [Cr03] - indeed, there are infinitely many disjoint such
monochromatic solutions.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos46.lean"]
theorem erdos_46 :
    answer(True) ↔
    -- For any finite colouring of the integers
    ∀ (𝓒 : ℕ → ℕ), (Set.range 𝓒).Finite →
      -- there are integers `2 ≤ n₁ < ⋯ < n_k`
      ∃ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) ∧
        -- whose reciprocals sum to `1`
        ∑ n ∈ S, (1 / n : ℚ) = 1 ∧
        -- and which all have the same colour
        (𝓒 '' (S : Set ℕ)).Subsingleton := by
  sorry

/--
Croot [Cr03] proved more: there are infinitely many disjoint such monochromatic solutions.
-/
@[category research solved, AMS 5 11]
theorem erdos_46.variants.infinitely_many_disjoint :
    answer(True) ↔
    ∀ (𝓒 : ℕ → ℕ), (Set.range 𝓒).Finite →
      ∃ S : ℕ → Finset ℕ, (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
        ∀ i, (∀ n ∈ S i, 2 ≤ n) ∧ ∑ n ∈ S i, (1 / n : ℚ) = 1 ∧
          (𝓒 '' (S i : Set ℕ)).Subsingleton := by
  sorry

/--
In [ErGr80] they also ask for a monochromatic representation of any $\frac{a}{b}>0$.
-/
@[category research solved, AMS 5 11]
theorem erdos_46.variants.positive_rat :
    answer(True) ↔
    ∀ (𝓒 : ℕ → ℕ), (Set.range 𝓒).Finite → ∀ q : ℚ, 0 < q →
      ∃ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) ∧ ∑ n ∈ S, (1 / n : ℚ) = q ∧
        (𝓒 '' (S : Set ℕ)).Subsingleton := by
  sorry

end Erdos46
