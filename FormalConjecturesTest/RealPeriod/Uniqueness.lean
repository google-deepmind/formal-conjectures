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

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# A period lattice is determined by its invariants

If two period lattices have the same $g_2$ and $g_3$ then they are equal
(`PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq`). The proof is the classical one.

1. $\wp(z) = \wp^{\circ}(z) + z^{-2}$, where $\wp^{\circ}$ is analytic at $0$ with Taylor
   coefficients $(n+1)! \, G_{n+2}$.
2. The differential equation $\wp'^2 = 4 \wp^3 - g_2 \wp - g_3$ gives $\wp'' = 6 \wp^2 - g_2 / 2$,
   and hence a recursion expressing each Taylor coefficient of $\wp^{\circ}$ in terms of the
   earlier ones.
3. By strong induction all coefficients are determined by $g_2$ and $g_3$, so equal invariants
   give $\wp_1 = \wp_2$ near $0$, hence everywhere off the lattices by the identity theorem.
4. A lattice is the polar set of its $\wp$-function, so the lattices agree.

Ported from the LeanBridge development.
-/

open Filter Topology
open scoped Nat

namespace PeriodPair

noncomputable section

attribute [local fun_prop] AnalyticAt.contDiffAt

variable (L : PeriodPair)

/- ## The Laurent expansion of `℘` at `0` -/

/-- Points of a punctured neighbourhood of $0$ are not lattice points. -/
lemma eventually_notMem_lattice : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
    self_mem_nhdsWithin] with z hz (hz0 : z ≠ 0) hzL
  exact hz ⟨hzL, hz0⟩

/-- The pole part of $\wp$ at $0$, globally: at $z = 0$ both sides are the junk value $0$. -/
lemma weierstrassP_eq (z : ℂ) : ℘[L] z = ℘[L - (0 : ℂ)] z + 1 / z ^ 2 := by
  rw [← L.weierstrassPExcept_add 0 z]
  simp

/-- The pole part of $\wp'$ at $0$, globally. -/
lemma derivWeierstrassPExcept_zero_eq (z : ℂ) :
    ℘'[L - (0 : ℂ)] z = ℘'[L] z + 2 / z ^ 3 := by
  simpa using L.derivWeierstrassPExcept_def 0 z

/-- The Taylor coefficients of $\wp^{\circ}$ at $0$ are the Eisenstein series $G$. -/
lemma iteratedDeriv_weierstrassPExcept_zero (n : ℕ) :
    iteratedDeriv n ℘[L - (0 : ℂ)] 0 =
      if n = 0 then 0 else ((n + 1)! : ℂ) * L.G (n + 2) := by
  rw [L.iteratedDeriv_weierstrassPExcept_self 0]
  simp

/- ## The second-derivative differential equation `℘'' = 6℘² - g₂/2` -/

/-- $\wp'$ does not vanish in a punctured neighbourhood of $0$, where it behaves like
$-2 z^{-3}$. -/
lemma eventually_derivWeierstrassP_ne_zero :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), ℘'[L] z ≠ 0 := by
  have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), ℘'[L - (0 : ℂ)] z ∈ Metric.ball (0 : ℂ) 1 := by
    apply (L.analyticAt_derivWeierstrassPExcept 0).continuousAt.eventually_mem
    rw [L.derivWeierstrassPExcept_zero_zero]
    exact Metric.ball_mem_nhds _ one_pos
  have h2 : ∀ᶠ z : ℂ in 𝓝 0, z ∈ Metric.ball (0 : ℂ) 1 := Metric.ball_mem_nhds _ one_pos
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds, h2.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz1 hz2 (hz0 : z ≠ 0) hzero
  rw [mem_ball_zero_iff] at hz1 hz2
  rw [L.derivWeierstrassPExcept_zero_eq, hzero, zero_add, norm_div, norm_pow] at hz1
  have hz : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2', div_lt_one (by positivity)] at hz1
  have h3 : ‖z‖ ^ 3 < 1 := pow_lt_one₀ (norm_nonneg z) hz2 (by norm_num)
  linarith

/-- The second-derivative differential equation, in a punctured neighbourhood of $0$. -/
lemma eventually_deriv_derivWeierstrassP :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  filter_upwards [L.eventually_notMem_lattice, L.eventually_derivWeierstrassP_ne_zero]
    with z hz hz'
  have hev : (fun w ↦ ℘'[L] w ^ 2) =ᶠ[𝓝 z]
      fun w ↦ 4 * ℘[L] w ^ 3 - L.g₂ * ℘[L] w - L.g₃ := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact L.derivWeierstrassP_sq w hw
  have hd' : DifferentiableAt ℂ ℘'[L] z :=
    (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt
  have hd : DifferentiableAt ℂ ℘[L] z :=
    (L.analyticOnNhd_weierstrassP z hz).differentiableAt
  have hP : HasDerivAt ℘[L] (℘'[L] z) z := by
    simpa using hd.hasDerivAt
  have h1 := hd'.hasDerivAt.fun_pow 2
  have h2 := (((hP.fun_pow 3).const_mul (4 : ℂ)).fun_sub (hP.const_mul L.g₂)).sub_const L.g₃
  apply mul_left_cancel₀ (a := 2 * ℘'[L] z) (by simpa using hz')
  have hder := hev.deriv_eq
  rw [h1.deriv, h2.deriv] at hder
  push_cast at hder
  linear_combination hder

/-- The pole-cleared second-derivative equation as a germ at $0$:
$z^2 \wp''(z) = 6 z^2 f(z)^2 + 12 f(z) - \frac{g_2}{2} z^2$ where $f = \wp^{\circ}$. -/
lemma key_eventuallyEq :
    (fun z : ℂ ↦ z ^ 2 * deriv ℘'[L - (0 : ℂ)] z) =ᶠ[𝓝 (0 : ℂ)]
      fun z ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))
        + 12 * ℘[L - (0 : ℂ)] z - L.g₂ / 2 * z ^ 2 := by
  have h1 : (fun z : ℂ ↦ z ^ 2 * deriv ℘'[L - (0 : ℂ)] z) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun z ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))
        + 12 * ℘[L - (0 : ℂ)] z - L.g₂ / 2 * z ^ 2 := by
    filter_upwards [L.eventually_notMem_lattice, self_mem_nhdsWithin,
      L.eventually_deriv_derivWeierstrassP] with z hzL (hz0 : z ≠ 0) hD
    have hEq : ℘'[L - (0 : ℂ)] = fun w ↦ ℘'[L] w + 2 / w ^ 3 :=
      funext L.derivWeierstrassPExcept_zero_eq
    have hden : HasDerivAt (fun w : ℂ ↦ w ^ 3) (3 * z ^ 2) z := by
      simpa using hasDerivAt_pow 3 z
    have hz3 : HasDerivAt (fun w : ℂ ↦ 2 / w ^ 3) (-6 / z ^ 4) z := by
      convert (hasDerivAt_const z (2 : ℂ)).div hden (pow_ne_zero 3 hz0) using 1
      · aesop
      · aesop
      · aesop
      field_simp
      ring
    have hd' : DifferentiableAt ℂ ℘'[L] z :=
      (L.analyticOnNhd_derivWeierstrassP z hzL).differentiableAt
    have hsum : HasDerivAt (fun w ↦ ℘'[L] w + 2 / w ^ 3)
        (deriv ℘'[L] z + -6 / z ^ 4) z := hd'.hasDerivAt.add hz3
    rw [hEq, hsum.deriv, hD, L.weierstrassP_eq z]
    field_simp
    ring
  have h2 : (fun z : ℂ ↦ z ^ 2 * deriv ℘'[L - (0 : ℂ)] z) =ᶠ[pure (0 : ℂ)]
      (fun z ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))
        + 12 * ℘[L - (0 : ℂ)] z - L.g₂ / 2 * z ^ 2) :=
    Filter.eventually_pure.mpr (by simp)
  have h12 := Filter.eventually_sup.mpr ⟨h1, h2⟩
  rwa [nhdsNE_sup_pure] at h12

/- ## The coefficient recursion -/

/-- Leibniz collapse: the $n$-th derivative of $z^2 g(z)$ at $0$ for analytic $g$. -/
lemma iteratedDeriv_sq_mul (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0) {n : ℕ} (hn : 2 ≤ n) :
    iteratedDeriv n (fun z : ℂ ↦ z ^ 2 * g z) 0 =
      (n : ℂ) * ((n : ℂ) - 1) * iteratedDeriv (n - 2) g 0 := by
  have e : iteratedDeriv n (fun z : ℂ ↦ z ^ 2 * g z) 0 =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv i (· ^ 2 : ℂ → ℂ) 0 *
        iteratedDeriv (n - i) g 0 :=
    iteratedDeriv_fun_mul (by fun_prop) hg.contDiffAt
  rw [e, Finset.sum_eq_single_of_mem 2 (Finset.mem_range.mpr (by omega))
    (fun i _ hi ↦ by rw [iteratedDeriv_fun_pow_zero, if_neg hi]; ring),
    iteratedDeriv_fun_pow_zero, if_pos rfl, Nat.cast_choose_two]
  norm_num [Nat.factorial_two]

/-- The recursion: for $n \geq 3$, the $n$-th Taylor coefficient of $\wp^{\circ}$ at $0$ is
determined by the earlier ones. -/
lemma recursion {n : ℕ} (hn : 3 ≤ n) :
    ((n : ℂ) * ((n : ℂ) - 1) - 12) * iteratedDeriv n ℘[L - (0 : ℂ)] 0 =
      6 * ((n : ℂ) * ((n : ℂ) - 1)) * ∑ k ∈ Finset.range (n - 1),
        ((n - 2).choose k : ℂ) * iteratedDeriv k ℘[L - (0 : ℂ)] 0 *
          iteratedDeriv (n - 2 - k) ℘[L - (0 : ℂ)] 0 := by
  have hfa : AnalyticAt ℂ ℘[L - (0 : ℂ)] 0 := L.analyticAt_weierstrassPExcept 0
  -- the `n`-th derivative of the left-hand side of `key_eventuallyEq`
  have hL : iteratedDeriv n (fun z : ℂ ↦ z ^ 2 * deriv ℘'[L - (0 : ℂ)] z) 0 =
      (n : ℂ) * ((n : ℂ) - 1) * iteratedDeriv n ℘[L - (0 : ℂ)] 0 := by
    rw [iteratedDeriv_sq_mul _ ((L.analyticAt_derivWeierstrassPExcept 0).deriv) (by omega)]
    congr 1
    rw [← iteratedDeriv_succ', show n - 2 + 1 = n - 1 by omega,
      L.iteratedDeriv_derivWeierstrassPExcept_self 0,
      L.iteratedDeriv_weierstrassPExcept_zero n, if_neg (by omega),
      show n - 1 + 2 = n + 1 by omega, show n - 1 + 3 = n + 2 by omega, sumInvPow_zero]
  -- the `n`-th derivative of the right-hand side, piece by piece
  have e1 : iteratedDeriv n (fun z : ℂ ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))
        + 12 * ℘[L - (0 : ℂ)] z - L.g₂ / 2 * z ^ 2) 0 =
      iteratedDeriv n (fun z : ℂ ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))
        + 12 * ℘[L - (0 : ℂ)] z) 0 - iteratedDeriv n (fun z : ℂ ↦ L.g₂ / 2 * z ^ 2) 0 :=
    iteratedDeriv_fun_sub (by fun_prop) (by fun_prop)
  have e2 : iteratedDeriv n (fun z : ℂ ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))
        + 12 * ℘[L - (0 : ℂ)] z) 0 =
      iteratedDeriv n (fun z : ℂ ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))) 0
        + iteratedDeriv n (fun z : ℂ ↦ 12 * ℘[L - (0 : ℂ)] z) 0 :=
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop)
  have e3 : iteratedDeriv n (fun z : ℂ ↦ L.g₂ / 2 * z ^ 2) 0 = 0 := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero, if_neg (by omega)]
    simp
  have e4 : iteratedDeriv n (fun z : ℂ ↦ 12 * ℘[L - (0 : ℂ)] z) 0 =
      12 * iteratedDeriv n ℘[L - (0 : ℂ)] 0 := by
    rw [iteratedDeriv_const_mul_field]
  have e5 : iteratedDeriv n
        (fun z : ℂ ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z))) 0 =
      6 * ((n : ℂ) * ((n : ℂ) - 1) *
        iteratedDeriv (n - 2) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) 0) := by
    rw [iteratedDeriv_const_mul_field]
    congr 1
    exact iteratedDeriv_sq_mul _ (hfa.mul hfa) (by omega)
  have e6 : iteratedDeriv (n - 2) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) 0 =
      ∑ k ∈ Finset.range (n - 1), ((n - 2).choose k : ℂ) * iteratedDeriv k ℘[L - (0 : ℂ)] 0 *
        iteratedDeriv (n - 2 - k) ℘[L - (0 : ℂ)] 0 := by
    have e : iteratedDeriv (n - 2) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) 0 =
        ∑ k ∈ Finset.range (n - 2 + 1), ((n - 2).choose k : ℂ) *
          iteratedDeriv k ℘[L - (0 : ℂ)] 0 * iteratedDeriv (n - 2 - k) ℘[L - (0 : ℂ)] 0 :=
      iteratedDeriv_fun_mul hfa.contDiffAt hfa.contDiffAt
    rw [e, show n - 2 + 1 = n - 1 by omega]
  have key := L.key_eventuallyEq.iteratedDeriv_eq n
  rw [hL, e1, e2, e3, e4, e5, e6] at key
  linear_combination key

/- ## The invariants determine all coefficients -/

/-- Two lattices with the same $g_2$ and $g_3$ have the same Taylor coefficients of
$\wp^{\circ}$ at $0$. -/
lemma iteratedDeriv_eq_of_invariants {L₁ L₂ : PeriodPair}
    (hg₂ : L₁.g₂ = L₂.g₂) (hg₃ : L₁.g₃ = L₂.g₃) (n : ℕ) :
    iteratedDeriv n ℘[L₁ - (0 : ℂ)] 0 = iteratedDeriv n ℘[L₂ - (0 : ℂ)] 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hG4 : L₁.G 4 = L₂.G 4 := by
      have h := hg₂
      simp only [g₂] at h
      exact mul_left_cancel₀ (by norm_num) h
    have hG6 : L₁.G 6 = L₂.G 6 := by
      have h := hg₃
      simp only [g₃] at h
      exact mul_left_cancel₀ (by norm_num) h
    rcases lt_or_ge n 5 with hn | hn
    · interval_cases n
      · simp [iteratedDeriv_weierstrassPExcept_zero]
      · simp [iteratedDeriv_weierstrassPExcept_zero,
          L₁.G_eq_zero_of_odd 3 (by decide), L₂.G_eq_zero_of_odd 3 (by decide)]
      · simp [iteratedDeriv_weierstrassPExcept_zero, hG4]
      · simp [iteratedDeriv_weierstrassPExcept_zero,
          L₁.G_eq_zero_of_odd 5 (by decide), L₂.G_eq_zero_of_odd 5 (by decide)]
      · simp [iteratedDeriv_weierstrassPExcept_zero, hG6]
    · have h₁ := L₁.recursion (n := n) (by omega)
      have h₂ := L₂.recursion (n := n) (by omega)
      have hsum : ∑ k ∈ Finset.range (n - 1), ((n - 2).choose k : ℂ) *
            iteratedDeriv k ℘[L₁ - (0 : ℂ)] 0 * iteratedDeriv (n - 2 - k) ℘[L₁ - (0 : ℂ)] 0 =
          ∑ k ∈ Finset.range (n - 1), ((n - 2).choose k : ℂ) *
            iteratedDeriv k ℘[L₂ - (0 : ℂ)] 0 *
              iteratedDeriv (n - 2 - k) ℘[L₂ - (0 : ℂ)] 0 :=
        Finset.sum_congr rfl fun k hk ↦ by
          have hk' := Finset.mem_range.mp hk
          rw [ih k (by omega), ih (n - 2 - k) (by omega)]
      have h20 : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      have hcoef : ((n : ℂ) * ((n : ℂ) - 1) - 12) ≠ 0 := by
        have hne : n * (n - 1) ≠ 12 := by omega
        have hc : ((n : ℂ) * ((n : ℂ) - 1) - 12) = ((n * (n - 1) : ℕ) : ℂ) - 12 := by
          push_cast [Nat.cast_sub (show 1 ≤ n by omega)]
          ring
        rw [hc, sub_ne_zero]
        exact_mod_cast hne
      apply mul_left_cancel₀ hcoef
      rw [h₁, h₂, hsum]

/- ## From equal coefficients to equal `℘`, and to equal lattices -/

/-- Equal Taylor coefficients of $\wp^{\circ}$ at $0$ give $\wp_1 = \wp_2$ near $0$. -/
lemma weierstrassP_eventuallyEq {L₁ L₂ : PeriodPair}
    (h : ∀ n, iteratedDeriv n ℘[L₁ - (0 : ℂ)] 0 = iteratedDeriv n ℘[L₂ - (0 : ℂ)] 0) :
    ℘[L₁] =ᶠ[𝓝 (0 : ℂ)] ℘[L₂] := by
  have h₁ := (L₁.analyticAt_weierstrassPExcept 0).hasFPowerSeriesAt
  have h₂ := (L₂.analyticAt_weierstrassPExcept 0).hasFPowerSeriesAt
  have hp : (FormalMultilinearSeries.ofScalars ℂ
        fun n ↦ iteratedDeriv n ℘[L₁ - (0 : ℂ)] 0 / n !) =
      FormalMultilinearSeries.ofScalars ℂ
        fun n ↦ iteratedDeriv n ℘[L₂ - (0 : ℂ)] 0 / n ! := by
    congr 1
    funext n
    rw [h n]
  rw [hp] at h₁
  have hsub : HasFPowerSeriesAt (℘[L₁ - (0 : ℂ)] - ℘[L₂ - (0 : ℂ)])
      (0 : FormalMultilinearSeries ℂ ℂ ℂ) 0 := by
    simpa using h₁.sub h₂
  have hEq : ℘[L₁ - (0 : ℂ)] =ᶠ[𝓝 (0 : ℂ)] ℘[L₂ - (0 : ℂ)] := by
    filter_upwards [hsub.eventually_eq_zero] with z hz
    simpa [sub_eq_zero] using hz
  filter_upwards [hEq] with z hz
  rw [L₁.weierstrassP_eq z, L₂.weierstrassP_eq z, hz]

/-- $\wp_1 = \wp_2$ near $0$ gives $\wp_1 = \wp_2$ off the union of the two lattices, by the
identity theorem on that connected set. -/
lemma eqOn_weierstrassP {L₁ L₂ : PeriodPair} (hev : ℘[L₁] =ᶠ[𝓝 (0 : ℂ)] ℘[L₂]) :
    Set.EqOn ℘[L₁] ℘[L₂] ((L₁.lattice : Set ℂ) ∪ (L₂.lattice : Set ℂ))ᶜ := by
  have hc₁ : (L₁.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L₁.lattice)
  have hc₂ : (L₂.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L₂.lattice)
  have hct := hc₁.union hc₂
  have hpre : IsPreconnected ((L₁.lattice : Set ℂ) ∪ (L₂.lattice : Set ℂ))ᶜ :=
    (hct.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  obtain ⟨U, hUs, hUo, h0U⟩ := mem_nhds_iff.mp hev
  obtain ⟨z₀, hz₀c, hz₀U⟩ := (hct.dense_compl ℂ).exists_mem_open hUo ⟨0, h0U⟩
  have hev' : ℘[L₁] =ᶠ[𝓝 z₀] ℘[L₂] := by
    filter_upwards [hUo.mem_nhds hz₀U] with z hz
    exact hUs hz
  exact (L₁.analyticOnNhd_weierstrassP.mono
      (Set.compl_subset_compl.mpr Set.subset_union_left)).eqOn_of_preconnected_of_eventuallyEq
    (L₂.analyticOnNhd_weierstrassP.mono
      (Set.compl_subset_compl.mpr Set.subset_union_right)) hpre hz₀c hev'

/-- If $\wp_1 = \wp_2$ off the union of the lattices then $\Lambda_1 \subseteq \Lambda_2$: a
point of $\Lambda_1$ outside $\Lambda_2$ would be a pole of $\wp_1$ but not of $\wp_2$. -/
lemma lattice_le_of_eqOn {L₁ L₂ : PeriodPair}
    (h : Set.EqOn ℘[L₁] ℘[L₂] ((L₁.lattice : Set ℂ) ∪ (L₂.lattice : Set ℂ))ᶜ) :
    L₁.lattice ≤ L₂.lattice := by
  intro x hx
  by_contra hx₂
  have hev : ℘[L₁] =ᶠ[𝓝[≠] x] ℘[L₂] := by
    have hW : ((L₂.lattice : Set ℂ))ᶜ ∩ ((L₁.lattice : Set ℂ) \ {x})ᶜ ∈ 𝓝 x :=
      Filter.inter_mem (L₂.isClosed_lattice.isOpen_compl.mem_nhds hx₂)
        (L₁.compl_lattice_sdiff_singleton_mem_nhds x)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hW, self_mem_nhdsWithin]
      with z hz (hzx : z ≠ x)
    obtain ⟨hz₂, hz₁⟩ := hz
    refine h ?_
    rintro (hzL | hzL)
    · exact hz₁ ⟨hzL, hzx⟩
    · exact hz₂ hzL
  have h₁ : meromorphicOrderAt ℘[L₁] x = -2 := L₁.order_weierstrassP x hx
  have h₂ : (0 : WithTop ℤ) ≤ meromorphicOrderAt ℘[L₂] x :=
    (L₂.analyticOnNhd_weierstrassP x hx₂).meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr hev, h₁] at h₂
  exact absurd h₂ (by decide)

/- ## The uniqueness theorem -/

/-- **Uniqueness of the period lattice.** A period lattice is determined by its invariants
$g_2$ and $g_3$. -/
theorem lattice_eq_of_g₂_eq_of_g₃_eq {L₁ L₂ : PeriodPair}
    (hg₂ : L₁.g₂ = L₂.g₂) (hg₃ : L₁.g₃ = L₂.g₃) : L₁.lattice = L₂.lattice := by
  have hEqOn := eqOn_weierstrassP
    (weierstrassP_eventuallyEq (iteratedDeriv_eq_of_invariants hg₂ hg₃))
  refine le_antisymm (lattice_le_of_eqOn hEqOn) (lattice_le_of_eqOn ?_)
  rw [Set.union_comm]
  exact fun z hz ↦ (hEqOn hz).symm

end

end PeriodPair
