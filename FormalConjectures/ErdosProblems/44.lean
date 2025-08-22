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
# Erdős Problem 44: Extending Sidon Sets

*Reference:* [erdosproblems.com/44](https://www.erdosproblems.com/44)
-/

open Function Set

namespace Erdos44

-- Reference: https://arxiv.org/pdf/2103.15850
/-- The maximum size of a Sidon set in `{1, ..., N}` is less than or equal to `2 * √N`. -/
@[category undergraduate, AMS 5 11]
theorem maxSidonSetSize_bound (N : ℕ) (hN : 1 ≤ N) :
    maxSidonSetSize N ≤ 2 * Real.sqrt N := by
  sorry

/--
**Erdős Problem 44:** Let N ≥ 1 and `A ⊆ {1,…,N}` be a Sidon set. Is it true that, for any ε > 0,
there exist M = M(ε) and `B ⊆ {N+1,…,M}` such that `A ∪ B ⊆ {1,…,M}` is a Sidon set
of size at least `(1−ε)M^{1/2}`?

This problem asks whether any Sidon set can be extended to achieve a density
arbitrarily close to the optimal density for Sidon sets.
-/
@[category undergraduate, AMS 5 11]
theorem erdos_44 : (∀ᵉ (N ≥ (1 : ℕ)) (A ⊆ Finset.Icc 1 N), IsSidon A.toSet →
    ∀ᵉ (ε > (0 : ℝ)), ∃ᵉ (M > N) (B ⊆ Finset.Icc (N + 1) M),
      IsSidon (A ∪ B).toSet ∧ (1 - ε) * Real.sqrt M ≤ (A ∪ B).card) ↔ answer(sorry) := by
  sorry

/--
A variant considering the extension to any larger range.
-/
@[category undergraduate, AMS 5 11]
theorem erdos_44.variant : (∀ᵉ (N ≥ (1 : ℕ)) (A ⊆ Finset.Icc 1 N), IsSidon A.toSet →
    ∀ᵉ (ε > (0 : ℝ)) (M ≥ N), ∃ᵉ (B ⊆ Finset.Icc (N + 1) M),
      IsSidon (A ∪ B).toSet ∧ (1 - ε) * Real.sqrt M ≤ (A ∪ B).card) ↔ answer(sorry) := by
  sorry

/--
The case where we start with an empty set (constructing large Sidon sets).
-/
@[category research open, AMS 5 11]
theorem erdos_44.empty_start : (∀ᵉ (ε > (0 : ℝ)), ∃ᵉ (M : ℕ) (A ⊆ Finset.Icc 1 M),
    IsSidon A.toSet ∧ (1 - ε) * Real.sqrt M ≤ A.card) ↔ answer(sorry) := by
  sorry

/--
A constructive version asking for explicit bounds on M in terms of ε.
-/
@[category research open, AMS 5 11]
theorem erdos_44.constructive : (∃ (f : ℝ → ℕ), ∀ᵉ (N ≥ (1 : ℕ)) (A ⊆ Finset.Icc 1 N),
    IsSidon A.toSet → ∀ᵉ (ε > (0 : ℝ)), ∃ᵉ (M ≤ f ε) (B ⊆ Finset.Icc (N + 1) M),
      N < M ∧ IsSidon (A ∪ B).toSet ∧ (1 - ε) * Real.sqrt M ≤ (A ∪ B).card) ↔ answer(sorry) := by
  sorry

/-! ## Related results and examples -/

/--
The set `{1, 2, 4, 8, 13}` is a Sidon set in `{1, ..., 13}`.
-/
@[category undergraduate, AMS 5 11]
theorem example_sidon_set : IsSidon {1, 2, 4, 8, 13} := by
  sorry

/--
For any `N`, there exists a Sidon set of size at least `√N/2`.
-/
@[category undergraduate, AMS 5 11]
theorem sidon_set_lower_bound (N : ℕ) (hN : 1 ≤ N) :
    ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon A.toSet ∧ N.sqrt / 2 ≤ A.card := by
  sorry

/--
The greedy construction gives a Sidon set of size approximately `√N`.
-/
@[category undergraduate, AMS 5 11]
theorem greedy_sidon_construction (N : ℕ) (hN : 1 ≤ N) :
    ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon A.toSet ∧ A.card ≥ N.sqrt := by
  sorry

end Erdos44
