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

*References:*
- [erdosproblems.com/514](https://www.erdosproblems.com/514)
- [Ha60] Hayman, W. K., *On the growth of integral functions on asymptotic paths*. J. Indian
  Math. Soc. (N.S.) 24 (1960), 251--264.
- [HaLi18] Hayman, W. K. and Lingham, E. F., *Research problems in function theory*.
  [arXiv:1809.07200](https://arxiv.org/abs/1809.07200) (2018), Problem 2.6.
-/

@[expose] public section

open Filter Polynomial Set

namespace Erdos514

/-- `γ` is a path to infinity: it is continuous and $\lvert\gamma(t)\rvert\to\infty$ as
$t\to\infty$. Only the behaviour of `γ` as $t\to\infty$ matters. -/
def IsPathToInfinity (γ : ℝ → ℂ) : Prop :=
  Continuous γ ∧ Tendsto (fun t ↦ ‖γ t‖) atTop atTop

/-- The maximum modulus $M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

/-- `f` has infinite order: $\log M(r) > r^C$ for arbitrarily large $r$, for every $C$. -/
def IsOfInfiniteOrder (f : ℂ → ℂ) : Prop :=
  ∀ C : ℝ, ∃ᶠ r in atTop, Real.exp (r ^ C) < maxModulus f r

/-- `f` has finite order on every path on which $f\to\infty$: on each such path,
$\log\lvert f(z)\rvert\le\lvert z\rvert^C$ for some $C$ and all large $z$. -/
def HasFiniteOrderOnAsymptoticPaths (f : ℂ → ℂ) : Prop :=
  ∀ γ, IsPathToInfinity γ → Tendsto (fun t ↦ ‖f (γ t)‖) atTop atTop →
    ∃ C : ℝ, ∀ᶠ t in atTop, ‖f (γ t)‖ ≤ Real.exp (‖γ t‖ ^ C)

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

Boas (unpublished) has proved the first part, that such a path must exist. This is recorded in
[HaLi18, Problem 2.6].

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
Hayman [Ha60] proved that there exist entire functions of infinite order, growing arbitrarily
rapidly, such that on every path on which $f(z)\to\infty$ we have
$\log\log\lvert f(z)\rvert = O(\log\lvert z\rvert)$, that is, $f$ has finite order on the path.
See [HaLi18, Problem 2.6].

We state the consequence that such an $f$ has infinite order. Such an $f$ is transcendental
and has $M(r)\to\infty$, since both hold for every entire function of infinite order.
-/
@[category research solved, AMS 30]
theorem erdos_514.variants.hayman :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ Transcendental ℂ[X] f ∧
      Tendsto (maxModulus f) atTop atTop ∧ IsOfInfiniteOrder f ∧
      HasFiniteOrderOnAsymptoticPaths f := by
  sorry

/-- A function as in `erdos_514.variants.hayman` has no path on which
$\lvert f(z)\rvert / M(\lvert z\rvert)^\epsilon\to\infty$, for any $\epsilon>0$. So
`erdos_514.variants.hayman` implies `erdos_514.parts.iii`.

Such a path is a path on which $f\to\infty$, so $\lvert f(z)\rvert\le e^{\lvert z\rvert^C}$ on
it. The path meets every large circle, including those with $M(r) > e^{r^{C+1}}$. -/
@[category API, AMS 30]
theorem not_exists_fast_path {f : ℂ → ℂ} (hM : Tendsto (maxModulus f) atTop atTop)
    (hinf : IsOfInfiniteOrder f) (hfin : HasFiniteOrderOnAsymptoticPaths f) :
    ¬ ∃ ε > (0 : ℝ), ∃ γ, IsPathToInfinity γ ∧
      Tendsto (fun t ↦ ‖f (γ t)‖ / maxModulus f ‖γ t‖ ^ ε) atTop atTop := by
  rintro ⟨ε, hε, γ, hγ, hT⟩
  have hMγ : Tendsto (fun t ↦ maxModulus f ‖γ t‖ ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp (hM.comp hγ.2)
  have hfγ : Tendsto (fun t ↦ ‖f (γ t)‖) atTop atTop := by
    refine (hT.atTop_mul_atTop₀ hMγ).congr' ?_
    filter_upwards [hMγ.eventually_gt_atTop 0] with t ht
    exact div_mul_cancel₀ _ ht.ne'
  obtain ⟨C, hC⟩ := hfin γ hγ hfγ
  obtain ⟨T, hTT⟩ := eventually_atTop.1 (hC.and (hT.eventually_ge_atTop 1))
  obtain ⟨r, hMr, hr0, hrε, hrT⟩ := ((hinf (C + 1)).and_eventually
    ((eventually_gt_atTop 0).and ((eventually_ge_atTop (1 / ε)).and
      (eventually_ge_atTop ‖γ T‖)))).exists
  obtain ⟨t, ht, htr⟩ := intermediate_value_Ici hγ.1.norm.continuousOn hγ.2 hrT
  obtain ⟨hfC, h1⟩ := hTT t ht
  simp only at htr
  rw [htr] at hfC h1
  have hMpos : 0 < maxModulus f r := (Real.exp_pos _).trans hMr
  have hle : maxModulus f r ^ ε ≤ ‖f (γ t)‖ :=
    (one_le_div (Real.rpow_pos_of_pos hMpos ε)).1 h1
  have hεr : 1 ≤ ε * r := by rw [div_le_iff₀ hε] at hrε; linarith
  have hrC := Real.rpow_pos_of_pos hr0 C
  have hlt : Real.exp (r ^ C) < maxModulus f r ^ ε :=
    calc Real.exp (r ^ C) ≤ Real.exp (r ^ (C + 1) * ε) := by
          rw [Real.exp_le_exp, Real.rpow_add_one hr0.ne']
          nlinarith
      _ = Real.exp (r ^ (C + 1)) ^ ε := Real.exp_mul _ _
      _ < maxModulus f r ^ ε := Real.rpow_lt_rpow (Real.exp_pos _).le hMr hε
  linarith

/--
Can the length of this path be estimated in terms of
$M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$? Does there exist a path along which
$\lvert f(z)\rvert$ tends to $\infty$ faster than a fixed function of $M(r)$ (such as
$M(r)^\epsilon$)?

We formalise the last question for $M(r)^\epsilon$, with $\epsilon>0$ allowed to depend on $f$.
This is the weakest form of the question. The answer is no: the functions of Hayman [Ha60] have
no such path. See `erdos_514.variants.hayman` and `not_exists_fast_path`. The length estimate
has no precise claim to state and is not formalised.
-/
@[category research solved, question, AMS 30]
theorem erdos_514.parts.iii :
    ¬ ∀ f : ℂ → ℂ, Differentiable ℂ f → Transcendental ℂ[X] f →
      ∃ ε > (0 : ℝ), ∃ γ, IsPathToInfinity γ ∧
        Tendsto (fun t ↦ ‖f (γ t)‖ / maxModulus f ‖γ t‖ ^ ε) atTop atTop := by
  sorry

end Erdos514
