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

*References:*
- [erdosproblems.com/512](https://www.erdosproblems.com/512)
- [Ko81] Konyagin, S. V., *On the Littlewood problem*. Izv. Akad. Nauk SSSR Ser. Mat. (1981),
  243-265, 463.
- [MPS81] McGehee, O. Carruth and Pigno, Louis and Smith, Brent, *Hardy's inequality and the
  $L^1$ norm of exponential sums*. Ann. of Math. (2) (1981), 613-618.
-/

namespace Erdos512

/-- Shorthand for the additive character $e(x) = e^{2\pi i x}$. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

/--
Is it true that, if $A\subset \mathbb{Z}$ is a finite set of size $N$, then
\[\int_0^1 \left\lvert \sum_{n\in A}e(n\theta)\right\rvert \mathrm{d}\theta \gg \log N,\]
where $e(x)=e^{2\pi ix }$?

Littlewood's conjecture, proved independently by Konyagin [Ko81] and McGehee, Pigno, and
Smith [MPS81].
-/
@[category research solved, AMS 11 42]
theorem erdos_512 : answer(True) ↔
    ∃ c > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℤ), A.card = N →
      c * Real.log N ≤ ∫ θ in (0 : ℝ)..1, ‖∑ n ∈ A, e (n * θ)‖ := by
  sorry

end Erdos512
