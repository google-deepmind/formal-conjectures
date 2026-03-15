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
# Erdős Problem 1115

*Reference:* [erdosproblems.com/1115](https://www.erdosproblems.com/1115)

Let $f(z)$ be an entire function of finite order, and let $\Gamma$ be a rectifiable path
on which $f(z) \to \infty$. Let $\ell(r)$ be the length of $\Gamma$ in the disc $|z| < r$.
Can such a path $\Gamma$ always be found with $\ell(r) \ll r$?

[GoEr79] Gol'dberg, A. A. and Eremenko, A. È., *Asymptotic curves of entire functions of
finite order*. Mat. Sb. (N.S.) (1979), 555–581, 647.

[Ha60] Hayman, W. K., *Defective values and asymptotic paths*. Matematika (1960), 21–27.

[Ha60b] Hayman, W. K., *Slowly growing integral and subharmonic functions*. Comment. Math.
Helv. (1960), 75–84.

[Ha74] Hayman, W. K., *Research problems in function theory: new problems* (1974), 155–180.
-/

open Complex Filter Topology Set MeasureTheory

namespace Erdos1115

/-- An entire function: differentiable everywhere on $\mathbb{C}$. -/
def IsEntire (f : ℂ → ℂ) : Prop := Differentiable ℂ f

/-- An entire function has finite order: there exists $\rho \geq 0$ such that
    $|f(z)| \leq \exp(C \cdot |z|^\rho)$ for all sufficiently large $|z|$. -/
def HasFiniteOrder (f : ℂ → ℂ) : Prop :=
  ∃ ρ : ℝ, 0 ≤ ρ ∧ ∃ (C R : ℝ), 0 < R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (C * ‖z‖ ^ ρ)

/-- An arc-length parameterized rectifiable path in $\mathbb{C}$ going to infinity.
    The parameter $t$ represents arc length from the start. -/
structure ArcLengthPath where
  toFun : ℝ → ℂ
  continuous' : Continuous toFun
  /-- The path goes to infinity: $|\gamma(t)| \to \infty$ as $t \to \infty$. -/
  tendsToInfinity : Tendsto (fun t => ‖toFun t‖) atTop atTop
  /-- Parameterized by arc length: the variation on $[0, T]$ equals $T$. -/
  isArcLength : ∀ T : ℝ, 0 ≤ T → eVariationOn toFun (Icc 0 T) = ENNReal.ofReal T

/-- $f(z) \to \infty$ along a path $\gamma$. -/
def TendsToInfinityAlong (f : ℂ → ℂ) (γ : ArcLengthPath) : Prop :=
  Tendsto (fun t => ‖f (γ.toFun t)‖) atTop atTop

/-- The arc length of an arc-length parameterized path $\gamma$ inside the closed disk
    of radius $r$. For arc-length parameterization, this equals the Lebesgue measure
    of $\{t \geq 0 : |\gamma(t)| \leq r\}$. -/
noncomputable def pathLengthInDisk (γ : ArcLengthPath) (r : ℝ) : ℝ :=
  (volume (({t : ℝ | 0 ≤ t ∧ ‖γ.toFun t‖ ≤ r}) : Set ℝ)).toReal

/--
Erdős Problem 1115 (Disproved by Gol'dberg and Eremenko [GoEr79]):

Let $f(z)$ be an entire function of finite order, and let $\Gamma$ be a rectifiable path
on which $f(z) \to \infty$. Let $\ell(r)$ be the length of $\Gamma$ in the disc $|z| < r$.

Can such a path $\Gamma$ always be found with $\ell(r) \ll r$?

Disproved: Gol'dberg and Eremenko showed that for any $\varphi(r) \to \infty$ there is an
entire function $f$ with $\log M(r) \ll \varphi(r)(\log r)^2$ such that there is no path
$\Gamma$ on which $f(z) \to \infty$ and $\ell(r) \ll r$. They also construct such functions
of any prescribed finite order in $[0, \infty)$.

Formally: there exists an entire function of finite order such that for every
arc-length parameterized path to infinity on which $f \to \infty$, $\ell(r)$ is not $O(r)$.
-/
@[category research solved, AMS 30]
theorem erdos_1115 : answer(False) ↔
    ∀ f : ℂ → ℂ, IsEntire f → HasFiniteOrder f →
      ∃ γ : ArcLengthPath, TendsToInfinityAlong f γ ∧
        ∃ (C R : ℝ), ∀ r : ℝ, R ≤ r → pathLengthInDisk γ r ≤ C * r := by
  sorry

end Erdos1115
