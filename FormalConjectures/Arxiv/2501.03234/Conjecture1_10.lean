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
# Conjecture 1.10

*Reference:* [arxiv.org/pdf/2501.03234](https://arxiv.org/pdf/2501.03234)
**THEOREMS AND CONJECTURES ON AN ARITHMETIC SUM ASSOCIATED WITH THE CLASSICAL THETA FUNCTION θ₃**
by *Yan Yablonovskiy*
-/



open Nat Finset BigOperators in
theorem Conjecture1_10 (k: ℕ) (hprim: Nat.Prime k) (hodd: Odd k) : (∑ h ∈ range (k-2), (∑ j ∈ range (h-2),
    (-1:ℤ)^( (j+1) + 1 + (floor ((h+1)*(j+1) / k)) ) )) > 0 := by
  sorry
