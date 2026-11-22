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
# Erdős Problem 1117

*References:*
- [erdosproblems.com/1117](https://www.erdosproblems.com/1117)
- [Ha74] Hayman, W. K., *Research problems in function theory: new problems*. (1974), 155--180.
- [HePi68] Herzog, F. and Piranian, G., *The counting function for points of maximum modulus*.
  (1968), 240--243.
- [GlPa24] Glücksam, Adi and Pardo-Simón, Leticia, *An approximate solution to Erdős' maximum
  modulus points problem*. J. Math. Anal. Appl. (2024), Paper No. 127768, 20.
-/

@[expose] public section

namespace Erdos1117

open Filter
open scoped NNReal

/-- A monomial $f(z) = c z^n$. -/
def IsMonomial (f : ℂ → ℂ) : Prop :=
  ∃ c : ℂ, ∃ n : ℕ, f = fun z ↦ c * z ^ n

/--
The number of points $z$ with $\|z\| = r$ at which $\|f(z)\|$ attains its maximum on that circle.
`Nat.card` is `0` when this set is infinite. The count is finite for a non-monomial entire
function; that finiteness is not proved here.
-/
noncomputable def nu (f : ℂ → ℂ) (r : ℝ≥0) : ℕ :=
  Nat.card {z : ℂ // ‖z‖ = (r : ℝ) ∧ ∀ w : ℂ, ‖w‖ = (r : ℝ) → ‖f w‖ ≤ ‖f z‖}

/--
Let $f(z)$ be an entire function which is not a monomial. Let $\nu(r)$ count the number of $z$
with $\lvert z\rvert = r$ such that $\lvert f(z)\rvert = \max_{\lvert z\rvert = r}\lvert f(z)\rvert$.
(This is a finite quantity if $f$ is not a monomial.)

Is it possible for $\limsup \nu(r) = \infty$?

The answer to the first question is yes, as shown by Herzog and Piranian [HePi68]. This is
Problem 2.16 in [Ha74], where it is attributed to Erdős.
-/
@[category research solved, question, AMS 30]
theorem erdos_1117.parts.i :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ¬ IsMonomial f ∧
      atTop.limsup (fun r : ℝ≥0 ↦ (nu f r : EReal)) = ⊤ := by
  sorry

/--
Let $f(z)$ be an entire function which is not a monomial. Let $\nu(r)$ count the number of $z$
with $\lvert z\rvert = r$ such that $\lvert f(z)\rvert = \max_{\lvert z\rvert = r}\lvert f(z)\rvert$.
(This is a finite quantity if $f$ is not a monomial.)

Is it possible for $\liminf \nu(r) = \infty$?

The second question is still open, although an 'approximate' affirmative answer is given by
Glücksam and Pardo-Simón [GlPa24]. For $\mathbb{N}$-valued $\nu$, this is $\nu(r) \to \infty$.
-/
@[category research open, question, AMS 30]
theorem erdos_1117.parts.ii :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ¬ IsMonomial f ∧
      Tendsto (fun r : ℝ≥0 ↦ nu f r) atTop atTop := by
  sorry

end Erdos1117
