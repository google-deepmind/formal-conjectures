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
# Erdős Problem 512

*Reference:* [erdosproblems.com/512](https://www.erdosproblems.com/512)

This is Littlewood's conjecture, proved independently by Konyagin [Ko81]
and McGehee, Pigno, and Smith [MPS81].

[Ko81] Konyagin, S.V., _On a problem of Littlewood_, Izv. Akad. Nauk SSSR Ser. Mat.
45 (1981), 243–265.

[MPS81] McGehee, O.C., Pigno, L., and Smith, B., _Hardy's inequality and the $L^1$
norm of exponential sums_, Ann. of Math. 113 (1981), 613–618.
-/

open Finset BigOperators MeasureTheory

namespace Erdos512

/-- The exponential sum $\sum_{n \in A} e(n\theta)$ where $e(x) = e^{2\pi ix}$. -/
noncomputable def expSum512 (A : Finset ℤ) (θ : ℝ) : ℂ :=
  ∑ n ∈ A, Complex.exp (2 * ↑Real.pi * ↑n * ↑θ * Complex.I)

/-- Erdős Problem 512 (Littlewood's conjecture [Ko81] [MPS81]): There exists an absolute
constant $C > 0$ such that for every finite set $A \subset \mathbb{Z}$ with $|A| \geq 2$,
$$\int_0^1 \left| \sum_{n \in A} e(n\theta) \right| d\theta \geq C \cdot \log |A|.$$ -/
@[category research solved, AMS 42]
theorem erdos_512 :
    ∃ C : ℝ, 0 < C ∧
      ∀ A : Finset ℤ, 2 ≤ A.card →
        C * Real.log (A.card : ℝ) ≤
          ∫ θ in (0 : ℝ)..1, ‖expSum512 A θ‖ := by
  sorry

end Erdos512
