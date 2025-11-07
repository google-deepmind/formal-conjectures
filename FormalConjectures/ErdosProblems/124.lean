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

open Nat Finset Filter
open scoped Real

namespace Erdos124

/-!
# Erdős Problem 124

*References:*
- [erdosproblems.com/124](https://www.erdosproblems.com/124)
- [BEGL96] Burr, S. A. and Erdős, P. and Graham, R. L. and Li, W. Wen-Ching, Complete sequences of sets of integer powers. Acta Arith. (1996), 133-138.
-/

/--
Let $3\leq d_1 < d_2 < \cdots < d_k$ be integers such that
$$\sum_{1\leq i\leq k}\frac{1}{d_i-1}\geq 1.$$
Can all sufficiently large integers be written as a sum of the shape $\sum_i c_ia_i$
where $c_i\in \{0, 1\}$ and $a_i$ has only the digits $0, 1$ when written in base $d_i$?

Conjectured by Burr, Erdős, Graham, and Li [BEGL96]
-/
@[category research open, AMS 11]
theorem erdos_124 : (∀ k, ∀ d : Fin k → ℕ,
    ∀ i, 3 ≤ d i →  StrictMono d → ∑ i : Fin k, (1 : ℚ) / d i - 1 = 1 →
    ∀ᶠ n in atTop, ∃ c : Fin k → ℕ, ∃ a : Fin k → ℕ,
    ∀ i, c i ∈ ({0, 1} : Finset ℕ) ∧
    ∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1} ∧
    n = ∑ i, (c i) * (a i )) ↔ answer(sorry) := by
  sorry

-- TODO(firsching): formalize the other two claims from the additional material

end Erdos124
