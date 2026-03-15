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
# Erdős Problem 1001

*Reference:* [erdosproblems.com/1001](https://www.erdosproblems.com/1001)

Let $S(N, A, c)$ be the Lebesgue measure of the set of $\alpha \in (0,1)$ such that
$|\alpha - x/y| < A/y^2$
for some $N \leq y \leq cN$ and $\gcd(x,y) = 1$. Does
$\lim_{N \to \infty} S(N, A, c) = f(A, c)$
exist? What is its explicit form?

A problem of Erdős, Szüsz, and Turán [EST58], who proved the formula
$f(A, c) = 12A \log c / \pi^2$
when $0 < A < c/(1 + c^2)$.

The existence of the limit was proved by Kesten and Sós [KeSo66].
Alternative, more explicit proofs were given by Boca [Bo08] and
Xiong–Zaharescu [XiZa06].

[Er64b] Erdős, P., _Problems and results on diophantine approximations_.
Compositio Math. (1964), 52–65.

[EST58] Erdős, P., Szüsz, P., and Turán, P., _Remarks on the theory of
diophantine approximation_. Colloq. Math. (1958), 119–126.

[KeSo66] Kesten, H. and Sós, V. T., _On two problems of Erdős, Szüsz and
Turán concerning diophantine approximations_. Acta Arith. (1966/67), 183–192.

[Bo08] Boca, F. P., _A problem of Erdős, Szüsz and Turán concerning
Diophantine approximations_. Int. J. Number Theory (2008), 691–708.

[XiZa06] Xiong, M. and Zaharescu, A., _A problem of Erdős-Szüsz-Turán on
Diophantine approximation_. Acta Arith. (2006), 163–177.
-/

open MeasureTheory Set Filter

namespace Erdos1001

/-- The set of $\alpha \in (0,1)$ approximable by a coprime fraction $x/y$
    with $N \leq y \leq cN$ to within $A/y^2$. -/
noncomputable def approxSet (N : ℕ) (A c : ℝ) : Set ℝ :=
  {α : ℝ | α ∈ Ioo 0 1 ∧
    ∃ (x : ℤ) (y : ℕ), N ≤ y ∧ (y : ℝ) ≤ c * N ∧
      Nat.Coprime (Int.natAbs x) y ∧
      |α - (x : ℝ) / (y : ℝ)| < A / ((y : ℝ) ^ 2)}

/-- $S(N, A, c)$ is the Lebesgue measure of the approximation set. -/
noncomputable def sMeasure (N : ℕ) (A c : ℝ) : ℝ :=
  (volume (approxSet N A c)).toReal

/--
Erdős Problem 1001 [Er64b]:

For all $A > 0$ and $c > 1$, the limit $\lim_{N \to \infty} S(N, A, c)$ exists.

Proved by Kesten and Sós [KeSo66].
-/
@[category research solved, AMS 11 28]
theorem erdos_1001 : answer(True) ↔
    ∀ (A c : ℝ), 0 < A → 1 < c →
      ∃ L : ℝ, Tendsto (fun N : ℕ => sMeasure N A c) atTop (nhds L) := by
  sorry

/--
Erdős Problem 1001 — EST58 explicit formula [EST58]:

When $0 < A < c/(1 + c^2)$, the limit $f(A, c) = 12A \log c / \pi^2$.

Proved by Erdős, Szüsz, and Turán.
-/
@[category research solved, AMS 11 28]
theorem erdos_1001_explicit_formula :
    ∀ (A c : ℝ), 0 < A → 1 < c → A < c / (1 + c ^ 2) →
      Tendsto (fun N : ℕ => sMeasure N A c) atTop
        (nhds (12 * A * Real.log c / Real.pi ^ 2)) := by
  sorry

end Erdos1001
