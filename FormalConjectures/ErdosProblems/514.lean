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
# Erdős Problem 514

*Reference:* [erdosproblems.com/514](https://www.erdosproblems.com/514)
-/

@[expose] public section

open Filter Polynomial

namespace Erdos514

/-- `γ` is a path to infinity: it is continuous and $\lvert\gamma(t)\rvert\to\infty$ as
$t\to\infty$. Only the behaviour of `γ` as $t\to\infty$ matters. -/
def IsPathToInfinity (γ : ℝ → ℂ) : Prop :=
  Continuous γ ∧ Tendsto (fun t ↦ ‖γ t‖) atTop atTop

/-- The maximum modulus $M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

/-- The maximum modulus of a constant function is its absolute value. -/
@[category test, AMS 30]
theorem maxModulus_const (c : ℂ) {r : ℝ} (hr : 0 ≤ r) : maxModulus (fun _ ↦ c) r = ‖c‖ := by
  have : Nonempty {z : ℂ // ‖z‖ = r} := ⟨⟨r, by simp [abs_of_nonneg hr]⟩⟩
  exact ciSup_const

/-- The positive real axis is a path to infinity. -/
@[category test, AMS 30]
theorem isPathToInfinity_ofReal : IsPathToInfinity (fun t : ℝ ↦ (t : ℂ)) := by
  refine ⟨Complex.continuous_ofReal, ?_⟩
  simp only [Complex.norm_real, Real.norm_eq_abs]
  exact tendsto_abs_atTop_atTop

/-- The conclusion of `erdos_514.parts.i` holds for $f=\exp$ along the positive real axis. -/
@[category test, AMS 30]
theorem exp_div_pow_along_ofReal (n : ℕ) :
    Tendsto (fun t : ℝ ↦ ‖Complex.exp t / (t : ℂ) ^ n‖) atTop atTop := by
  refine (Real.tendsto_exp_div_pow_atTop n).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  simp [Complex.norm_exp_ofReal, abs_of_nonneg ht]

/-- Polynomial functions are not transcendental, so they are excluded from the problems below. -/
@[category test, AMS 30]
theorem not_transcendental_polynomial (p : ℂ[X]) : ¬ Transcendental ℂ[X] (fun z ↦ p.eval z) := by
  intro h
  apply h
  refine ⟨X - C p, X_sub_C_ne_zero p, ?_⟩
  funext z
  simp

/-- The transcendence hypothesis is needed: for $f(z)=z$ no path has
$\lvert f(z)/z^2\rvert\to\infty$. -/
@[category test, AMS 30]
theorem not_exists_path_id :
    ¬ ∃ γ, IsPathToInfinity γ ∧ Tendsto (fun t ↦ ‖γ t / γ t ^ 2‖) atTop atTop := by
  rintro ⟨γ, ⟨-, hγ⟩, h⟩
  have h0 : Tendsto (fun t ↦ ‖γ t / γ t ^ 2‖) atTop (nhds 0) := by
    refine (tendsto_inv_atTop_zero.comp hγ).congr fun t ↦ ?_
    simp [pow_two]
  exact not_tendsto_nhds_of_tendsto_atTop h 0 h0

/--
Let $f(z)$ be an entire transcendental function. Does there exist a path $L$ so that, for every
$n$,
$$\lvert f(z)/z^n\rvert \to \infty$$
as $z\to \infty$ along $L$?

Boas (unpublished) proved that such a path exists.

A path is a continuous `γ : ℝ → ℂ` with $\lvert\gamma(t)\rvert\to\infty$, and "$z\to\infty$
along $L$" means $t\to\infty$. Transcendence is `Transcendental ℂ[X] f`, as in Problem 513.
-/
@[category research solved, question, AMS 30]
theorem erdos_514.parts.i :
    ∀ f : ℂ → ℂ, Differentiable ℂ f → Transcendental ℂ[X] f →
      ∃ γ, IsPathToInfinity γ ∧
        ∀ n : ℕ, Tendsto (fun t ↦ ‖f (γ t) / γ t ^ n‖) atTop atTop := by
  sorry

/--
Let $f(z)$ be an entire transcendental function and
$M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$. Does there exist a path along which
$\lvert f(z)\rvert$ tends to $\infty$ faster than a fixed function of $M(r)$, such as
$M(r)^\epsilon$?

We formalise the example $M(r)^\epsilon$ with $\epsilon>0$ allowed to depend on $f$. This is the
weakest form of the question: a negative answer to it is a negative answer for every fixed
$\epsilon$. The second part of the problem, an estimate for the length of the path in terms of
$M(r)$, has no precise claim to state and is not formalised.
-/
@[category research open, question, AMS 30]
theorem erdos_514.parts.iii :
    ∀ f : ℂ → ℂ, Differentiable ℂ f → Transcendental ℂ[X] f →
      ∃ ε > (0 : ℝ), ∃ γ, IsPathToInfinity γ ∧
        Tendsto (fun t ↦ ‖f (γ t)‖ / maxModulus f ‖γ t‖ ^ ε) atTop atTop := by
  sorry

end Erdos514
