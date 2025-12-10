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
# Erdős Problem 1105

*Reference:* [erdosproblems.com/1105](https://www.erdosproblems.com/1105)
-/

namespace Erdos1105

open Classical

/-- The linear coefficient conjectured for `AR(n, C_k)`. -/
noncomputable def cycleCoeff (k : ℕ) : ℝ :=
  (Nat.choose (k - 2) 2 : ℝ) + (1 : ℝ) / (k - 1)

/-- ℓ = ⌊(k - 1)/2⌋. -/
def ell (k : ℕ) : ℕ :=
  (k - 1) / 2

/-- ε = 1 if k is odd, ε = 2 otherwise. -/
def eps (k : ℕ) : ℕ :=
  if k % 2 = 1 then 1 else 2

/--
Is it true that the anti-Ramsey number $AR(n, C_k)$ for cycles satisfies
$AR(n, C_k) = \binom{k-2}{2} + \frac{1}{k-1} \cdot n + O(1)$ for $k \geq 3$,
and the anti-Ramsey number $AR(n, P_k)$ for paths of length $k$ (where $k \geq 5$ and $n \geq k$)
is exactly $\max\left(\binom{k-2}{2} + 1, \binom{\ell-1}{2} + (\ell-1)(n-\ell+1) + \varepsilon\right)$
where $\ell = \lfloor(k-1)/2\rfloor$ and $\varepsilon = 1$ if $k$ is odd, $\varepsilon = 2$ otherwise?
-/
@[category research open, AMS 5]
theorem erdos_1105 :
    (∃ (AR_cycle AR_path : ℕ → ℕ → ℕ),
        -- Cycle part:  AR(n, C_k) = cycleCoeff(k) * n + O(1)
        (∀ k : ℕ, 3 ≤ k →
          ∃ C : ℝ, ∃ N0 : ℕ, 0 ≤ C ∧
            ∀ n : ℕ, n ≥ N0 →
              |(AR_cycle n k : ℝ) - cycleCoeff k * (n : ℝ)| ≤ C)
        ∧
        -- Path part:  exact formula for AR(n, P_k)
        (∀ n k : ℕ, n ≥ k → 5 ≤ k →
          AR_path n k =
            max
              (Nat.choose (k - 2) 2 + 1)
              (Nat.choose (ell k - 1) 2
                + (ell k - 1) * (n - ell k + 1)
                + eps k))
    ) ↔ answer(sorry) := by
  sorry

end Erdos1105
