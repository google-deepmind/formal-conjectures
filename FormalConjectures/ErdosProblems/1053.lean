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
# Erdős Problem 1053

*Reference:* [erdosproblems.com/1053](https://www.erdosproblems.com/1053)
-/

open scoped ArithmeticFunction

def Nat.Multiperfect (n : ℕ) (k : ℕ) : Prop := 0 < n ∧ σ 1 n = k * n

theorem Nat.perfect_iff_multiperfect_two {n : ℕ} : n.Perfect ↔ n.Multiperfect 2 := by
  simp [Perfect, Multiperfect, ArithmeticFunction.sigma_one_apply,
    Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

namespace Erdos1053

/-- Call a number $k$-perfect if $\sigma(n) = kn$, where $\sigma(n)$ is the sum of the
divisors of $n$. Must $k = o(\log\log n)$? -/
@[category research open, AMS 11]
theorem erdos_1053 :
    ∀ C > 0, ∀ᶠ n : ℕ in Filter.atTop, ∀ k,
      n.Multiperfect k → ‖(k : ℝ)‖ ≤ C * ‖Real.log (Real.log n)‖  := sorry

/-- Guy further writes 'It has even been suggested that there may be only finitely
many $k$-perfect numbers with $k \geq 3$.' -/
@[category research open, AMS 11]
theorem erdos_1053.variants.finite {k : ℕ} (hk : 3 ≤ k) :
    { n : ℕ | n.Multiperfect k }.Finite := sorry

end Erdos1053
