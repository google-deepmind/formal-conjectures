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
# Erdős Problem 1053

*References:*
- [erdosproblems.com/1053](https://www.erdosproblems.com/1053)
- [Gu04] Guy, Richard K., Unsolved problems in number theory. Springer-Verlag, New York (2004).
-/

open ArithmeticFunction Filter
open scoped ArithmeticFunction.sigma

namespace Erdos1053

/--
Must $k=o(\log\log n)$?

A question of Erdős, as reported in problem B2 of Guy's collection [Gu04].
-/
@[category research open, AMS 11]
theorem erdos_1053 :
    answer(sorry) ↔
      (fun n : ℕ ↦ (σ 1 n : ℝ) / (n : ℝ)) =o[atTop ⊓ 𝓟 {n : ℕ | ∃ k, Nat.IsPerfectFor n 1 k}]
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) := by
  sorry

/--
Guy further writes 'It has even been suggested that there may be only finitely many $k$-perfect
numbers with $k\geq 3$.'
-/
@[category research open, AMS 11]
theorem erdos_1053.variants.guy :
    answer(sorry) ↔ ∀ k ≥ 3, { n : ℕ | Nat.IsPerfectFor n 1 k }.Finite := by
  sorry

end Erdos1053
