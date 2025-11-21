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
# Erdős Problem 952

*Reference:* [erdosproblems.com/952](https://www.erdosproblems.com/952)
-/


namespace Erdos952

/--
Is there an infinite sequence of distinct Gaussian primes $x_1,x_2,\ldots$
such that $\lvert x_{n+1}-x_n\rvert \ll 1$?
-/
@[category research open, AMS 11]
theorem erdos_952 :
  ∃ (f : ℕ → GaussianInt), ∃ (B : ℤ),
    Function.Injective f ∧
      (∀ n, Prime (f n) ∧ (f (n + 1) - f n).norm ≤ B) := by
  sorry

end Erdos952
