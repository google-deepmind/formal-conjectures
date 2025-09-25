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
# Erdős Problem 330

*Reference:* [erdosproblems.com/330](https://www.erdosproblems.com/330)

Suppose `A ⊂ ℕ` is a minimal basis with positive density.
Is it true that, for any `n ∈ A`, the (upper) density of integers which cannot be
represented without using `n` is positive?
-/

namespace FormalConjectures
namespace ErdosProblems
namespace «330»

/-- `Basis A h` means `A` is a minimal asymptotic basis of order `h`. -/
def Basis (A : Set ℕ) (h : ℕ) : Prop := sorry

/--
**Erdős 330 — Conjecture (statement only).**

If `A` is a minimal basis of order `h ≥ 2` with positive density, then for every `n ∈ A`,
the set of integers which cannot be represented without using `n` has positive density.
-/
@[category research open, AMS 5]
theorem erdos_330 :
    ∀ (h : ℕ) (A : Set ℕ),
      2 ≤ h →
      Basis A h →
      A.HasPosDensity →
      (∀ n ∈ A, ({m | ¬ Basis (A \ {n}) h}).HasPosDensity) := by
  sorry

end «330»
end ErdosProblems
end FormalConjectures
