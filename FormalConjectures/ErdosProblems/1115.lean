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

import FormalConjecturesUtil

/-!
# Erdős Problem 1115

*References:*
- [erdosproblems.com/1115](https://www.erdosproblems.com/1115)
- [GoEr79] Gol'dberg, A. A. and Eremenko, A. È., *Asymptotic curves of entire functions of finite
  order*. Mat. Sb. (N.S.) (1979), 555--581, 647.
- [Ha60] W. Hayman, *Defective values and asymptotic paths*. Matematika (1960), 21-27.
- [Ha60b] Hayman, W. K., *Slowly growing integral and subharmonic functions*. Comment. Math. Helv.
  (1960), 75--84.
- [Ha74] Hayman, W. K., *Research problems in function theory: new problems*. (1974), 155--180.
-/

open Filter Set Asymptotics Bornology
open scoped Topology NNReal ENNReal

namespace Erdos1115

/--
An entire function `f` is of finite order if there exist `c, a ≥ 0` such that
`‖f z‖ ≤ c * rexp (‖z‖ ^ a)` for all `z`.
-/
def OfFiniteOrder (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∃ c ≥ (0 : ℝ), ∃ a ≥ (0 : ℝ), ∀ z, ‖f z‖ ≤ c * Real.exp (‖z‖ ^ a)

/--
A locally rectifiable path tending to infinity: a continuous locally bounded-variation
parametrization `γ : ℝ≥0 → ℂ` with `γ(t) → ∞` as `t → ∞`.
-/
def IsRectifiablePathToInfinity (γ : ℝ≥0 → ℂ) : Prop :=
  Continuous γ ∧ LocallyBoundedVariationOn γ univ ∧ Tendsto γ atTop (cobounded ℂ)

/--
The maximum modulus $M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$.
-/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

/--
The length $\ell(r)$ of a path `γ` in the disc $\lvert z\rvert < r$, measured as the
total variation of the parametrization on `{t | ‖γ t‖ < r}`.
-/
noncomputable def lengthInDisc (γ : ℝ≥0 → ℂ) (r : ℝ) : ℝ≥0∞ :=
  eVariationOn γ {t | ‖γ t‖ < r}

/--
The relation $\ell(r)\ll r$: the length of `γ` in $\lvert z\rvert < r$ is $O(r)$ as
$r\to\infty$.
-/
def LengthBigORadius (γ : ℝ≥0 → ℂ) : Prop :=
  ∃ C : ℝ, ∀ᶠ r in atTop, lengthInDisc γ r ≤ ENNReal.ofReal (C * r)

/--
The order $\limsup_{r\to\infty} \log\log M(r)/\log r$ of an entire function.
-/
noncomputable def entireOrder (f : ℂ → ℂ) : ℝ≥0∞ :=
  limsup (fun r : ℝ ↦ ENNReal.ofReal
    (Real.log (Real.log (maxModulus f r)) / Real.log r)) atTop

/--
Let $f(z)$ be an entire function of finite order, and let $\Gamma$ be a rectifiable path on which
$f(z)\to \infty$. Let $\ell(r)$ be the length of $\Gamma$ in the disc $\lvert z\rvert<r$.

Find a path for which $\ell(r)$ grows as slowly as possible, and estimate $\ell(r)$ in terms of
$M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$.

In particular, can such a path $\Gamma$ be found for which $\ell(r)\ll r$?

A problem originally due to Hayman [Ha60], according to [GoEr79], although (confusingly) in the
book [Ha74] by Hayman it is attributed to Erdős, as Problem 2.41.

Hayman [Ha60b] proved that if $\log M(r) \ll (\log r)^2$ then there exists a path $\Gamma$ on
which $f(z)\to \infty$ and $\ell(r)=r$.

Disproved by Gol'dberg and Eremenko [GoEr79] who proved that for any function $\phi(r)$ which
$\to \infty$ as $r\to \infty$ there is an entire function $f$ such that
$$\log M(r) \ll \phi(r)(\log r)^2$$
and there is no path $\Gamma$ on which $f(z)\to \infty$ and $\ell(r) \ll r$. They also construct
such functions of any prescribed finite order in $[0,\infty)$.

Constants are excluded: a constant function never tends to infinity along a path.
-/
@[category research solved, AMS 30]
theorem erdos_1115 : answer(False) ↔
    ∀ (f : ℂ → ℂ), OfFiniteOrder f → (∃ z w, f z ≠ f w) →
      ∃ γ : ℝ≥0 → ℂ, IsRectifiablePathToInfinity γ ∧
        Tendsto (fun t ↦ f (γ t)) atTop (cobounded ℂ) ∧ LengthBigORadius γ := by
  sorry

/--
Hayman [Ha60b] proved that if $\log M(r) \ll (\log r)^2$ then there exists a path $\Gamma$ on
which $f(z)\to \infty$ and $\ell(r)=r$.
-/
@[category research solved, AMS 30]
theorem erdos_1115.variants.hayman {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnonconst : ∃ z w, f z ≠ f w)
    (hM : (fun r ↦ Real.log (maxModulus f r)) =O[atTop]
      fun r ↦ Real.log r ^ 2) :
    ∃ γ : ℝ≥0 → ℂ, IsRectifiablePathToInfinity γ ∧
      Tendsto (fun t ↦ f (γ t)) atTop (cobounded ℂ) ∧
      ∀ r > 0, lengthInDisc γ r = ENNReal.ofReal r := by
  sorry

/--
Gol'dberg and Eremenko [GoEr79] proved that for any function $\phi(r)$ which $\to \infty$ as
$r\to \infty$ there is an entire function $f$ such that
$$\log M(r) \ll \phi(r)(\log r)^2$$
and there is no path $\Gamma$ on which $f(z)\to \infty$ and $\ell(r) \ll r$.
-/
@[category research solved, AMS 30]
theorem erdos_1115.variants.goldberg_eremenko {φ : ℝ → ℝ} (hφ : Tendsto φ atTop atTop) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z w, f z ≠ f w) ∧
      ((fun r ↦ Real.log (maxModulus f r)) =O[atTop]
        fun r ↦ φ r * Real.log r ^ 2) ∧
      ∀ γ : ℝ≥0 → ℂ, IsRectifiablePathToInfinity γ →
        Tendsto (fun t ↦ f (γ t)) atTop (cobounded ℂ) → ¬ LengthBigORadius γ := by
  sorry

/--
Gol'dberg and Eremenko [GoEr79] also construct such functions of any prescribed finite order in
$[0,\infty)$.
-/
@[category research solved, AMS 30]
theorem erdos_1115.variants.prescribed_order {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ f : ℂ → ℂ, OfFiniteOrder f ∧ (∃ z w, f z ≠ f w) ∧
      entireOrder f = ENNReal.ofReal ρ ∧
      ∀ γ : ℝ≥0 → ℂ, IsRectifiablePathToInfinity γ →
        Tendsto (fun t ↦ f (γ t)) atTop (cobounded ℂ) → ¬ LengthBigORadius γ := by
  sorry

/-- A constant path has variation zero in every disc. -/
@[category test, AMS 30]
theorem lengthInDisc_const (z : ℂ) (r : ℝ) : lengthInDisc (fun _ : ℝ≥0 ↦ z) r = 0 := by
  refine eVariationOn.constant_on ?_
  rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩
  rfl

/-- The length in $\lvert z\rvert < r$ vanishes for $r \le 0$, since the disc is empty. -/
@[category test, AMS 30]
theorem lengthInDisc_of_nonpos (γ : ℝ≥0 → ℂ) {r : ℝ} (hr : r ≤ 0) : lengthInDisc γ r = 0 := by
  have hempty : {t : ℝ≥0 | ‖γ t‖ < r} = ∅ := by
    ext t
    have : ¬ ‖γ t‖ < r := not_lt.mpr (hr.trans (norm_nonneg _))
    simp [this]
  rw [lengthInDisc, hempty]
  exact eVariationOn.subsingleton _ subsingleton_empty

/-- Constants are entire of finite order. -/
@[category test, AMS 30]
theorem ofFiniteOrder_const (a : ℂ) : OfFiniteOrder fun _ ↦ a := by
  refine ⟨by fun_prop, ‖a‖, norm_nonneg _, 1, zero_le_one, fun z ↦ ?_⟩
  exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (by positivity))

/-- On a nonempty circle the maximum modulus of a constant is the modulus of that constant. -/
@[category test, AMS 30]
theorem maxModulus_const (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    maxModulus (fun _ ↦ a) r = ‖a‖ := by
  have : Nonempty {z : ℂ // ‖z‖ = r} := ⟨⟨(r : ℂ), Complex.norm_of_nonneg hr⟩⟩
  exact ciSup_const

/-- On a nonempty circle the maximum modulus of the identity is the radius. -/
@[category test, AMS 30]
theorem maxModulus_id {r : ℝ} (hr : 0 ≤ r) : maxModulus (id : ℂ → ℂ) r = r := by
  have : Nonempty {z : ℂ // ‖z‖ = r} := ⟨⟨(r : ℂ), Complex.norm_of_nonneg hr⟩⟩
  have h : (fun z : {z : ℂ // ‖z‖ = r} ↦ ‖(z : ℂ)‖) = fun _ ↦ r := by
    ext z
    exact z.property
  simp [maxModulus, h, ciSup_const]

end Erdos1115
