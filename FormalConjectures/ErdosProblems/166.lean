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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 166

*References:*
- [erdosproblems.com/166](https://www.erdosproblems.com/166)
- [Sp77] Spencer, J., Asymptotic lower bounds for Ramsey functions. Discrete Math. (1977), 69-76.
- [AKS80] Ajtai, M., Komlós, J. and Szemerédi, E., A note on Ramsey numbers. J. Combin. Theory
  Ser. A (1980), 354-360.
- [MaVe23] Mattheus, S. and Verstraëte, J., The asymptotics of $r(4,t)$. Ann. of Math. (2024),
  941-965.
-/

@[expose] public section

open Filter

namespace Erdos166

/--
Prove that
$$R(4,k) \gg \frac{k^3}{(\log k)^{O(1)}}.$$

This is true, and was proved by Mattheus and Verstraëte [MaVe23], who showed that
$R(4,k) \gg \frac{k^3}{(\log k)^4}$.
This problem is #5 in Ramsey Theory in the graphs problem collection.
-/
@[category research solved, AMS 5]
theorem erdos_166 : answer(True) ↔
    ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∀ᶠ (k : ℕ) in atTop,
        (SimpleGraph.classicalRamsey 4 k : ℝ) ≥
          C * (k : ℝ) ^ 3 / (Real.log k) ^ c := by
  sorry

-- TODO: Add variants of the problem.

end Erdos166
