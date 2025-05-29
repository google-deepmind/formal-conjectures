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
# Erdős Problem 410

*Reference:* [erdosproblems.com/410](https://www.erdosproblems.com/410)
-/
open ArithmeticFunction Filter

/--
Let $σ_1(n) = σ(n)$, the sum of divisors function, and $σ_k(n) = σ(σ_{k−1}(n))$.

Is it true that $\lim_{k → ∞} σ_k(n)^{\frac 1 k} = ∞$?

This is problem (iii) from
Erdos, Granville, Pomerance, Spiro
"On the normal behavior of the iterates of some arithmetical functions"
(page 169 of the book "Analytic Number Theory", 1990).
-/
@[category research open, AMS 11]
theorem erdos_410 (n : ℕ) (hn : 1 < n) :
    Tendsto (fun k : ℕ ↦ ((sigma 1)^[k] n : ℝ) ^ (1 / (k : ℝ))) atTop atTop :=
  sorry
