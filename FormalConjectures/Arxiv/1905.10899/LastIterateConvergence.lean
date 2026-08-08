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

namespace Arxiv.«1905.10899»

/-!
# ODE Analysis of Stochastic Gradient Methods with Optimism and Anchoring for Minimax Problems

*Reference:* [arxiv/1905.10899](https://arxiv.org/abs/1905.10899)
by *Ernest K. Ryu, Kun Yuan, Wotao Yin*
-/



variable (n m : ℕ)

abbrev E_n := EuclideanSpace ℝ (Fin n)
abbrev F_m := EuclideanSpace ℝ (Fin m)
abbrev Z_space := WithLp 2 (E_n n × F_m m)

noncomputable def toProd : Z_space n m ≃L[ℝ] (E_n n × F_m m) :=
  WithLp.prodContinuousLinearEquiv _ _ _ _

structure State where
  z       : Z_space n m
  z0      : Z_space n m   -- Anchor point (fixed throughout)
  t       : ℕ
  history : List (Z_space n m)

-- Operator G(z) = (∇_x L(z), -∇_y L(z))
noncomputable def F_operator
  (L : (Z_space n m) → ℝ)
  (z : Z_space n m) : Z_space n m :=
  let g := toProd n m (gradient L z)
  (toProd n m).symm (g.1, -g.2)

noncomputable def IsSaddlePoint (L : Z_space n m → ℝ) (z_star : Z_space n m) : Prop :=
  let (x_star, y_star) := toProd n m z_star
  (∀ y : F_m m, L ((toProd n m).symm (x_star, y)) ≤ L z_star) ∧
  (∀ x : E_n n, L z_star ≤ L ((toProd n m).symm (x, y_star)))

-- Anchored Simultaneous Gradient Descent
-- z_{t+1} = z_t - α_t * G(z_t) + β_t * (z_0 - z_t)
noncomputable def step
  (L : (Z_space n m) → ℝ)
  (s : State n m)
  (grad_coeff anchor_coeff : ℝ)
  : State n m :=

  -- Query gradient at current point
  let g := F_operator n m L s.z

  -- Compute gradient step
  let grad_step := grad_coeff • g

  -- Compute anchor step: pulls toward z_0
  let anchor_step := anchor_coeff • (s.z0 - s.z)

  -- Final update: z_{t+1} = z_t - grad_step + anchor_step
  let z_next := s.z - grad_step + anchor_step

  {
    s with
    z := z_next,
    z0 := s.z0,
    t := s.t + 1,
    history := s.history ++ [z_next]
  }

noncomputable def coefficients_schedule
  (gamma K : ℝ)
  (t : ℕ) : ℝ × ℝ :=
  (1 / (K * Real.sqrt ((t : ℝ) + gamma)), gamma / ((t : ℝ) + gamma))

lemma inner_F_operator_self_ge_zero (n m : ℕ) (L : Z_space n m → ℝ)
  (h_monotone : ∀ z w : Z_space n m, inner ℝ (F_operator n m L z - F_operator n m L w) (z - w) ≥ (0 : ℝ))
  (z_star : Z_space n m) (h_opt : F_operator n m L z_star = 0) (z : Z_space n m) :
  inner ℝ (F_operator n m L z) (z - z_star) ≥ (0 : ℝ) := by
  have h := h_monotone z z_star
  rw [h_opt] at h
  have h_sub : F_operator n m L z - 0 = F_operator n m L z := sub_zero _
  rw [h_sub] at h
  exact h

lemma F_operator_lipschitz_bound (n m : ℕ) (L : Z_space n m → ℝ)
  (K : NNReal)
  (h_lipschitz : ∀ z w : Z_space n m, ‖F_operator n m L z - F_operator n m L w‖ ≤ K * ‖z - w‖)
  (z_star : Z_space n m) (h_opt : F_operator n m L z_star = 0) (z : Z_space n m) :
  ‖F_operator n m L z‖ ≤ K * ‖z - z_star‖ := by
  have h := h_lipschitz z z_star
  rw [h_opt] at h
  have h_sub : F_operator n m L z - 0 = F_operator n m L z := sub_zero _
  rw [h_sub] at h
  exact h

lemma z0_eq (n m : ℕ) (L : Z_space n m → ℝ)
  (gamma K : ℝ)
  (s_seq : ℕ → State n m)
  (z_init : Z_space n m)
  (h_init : s_seq 0 = { z := z_init, z0 := z_init, t := 0, history := [z_init]})
  (h_step : ∀ t, s_seq (t + 1) = step n m L (s_seq t) (coefficients_schedule gamma K t).1 (coefficients_schedule gamma K t).2) :
  ∀ t : ℕ, (s_seq t).z0 = z_init := by
  intro t
  induction t with
  | zero => rw [h_init]
  | succ t ih => rw [h_step t]; exact ih

lemma z_update_eq (n m : ℕ) (L : Z_space n m → ℝ)
  (gamma K : ℝ)
  (s_seq : ℕ → State n m)
  (z_init : Z_space n m)
  (h_init : s_seq 0 = { z := z_init, z0 := z_init, t := 0, history := [z_init]})
  (h_step : ∀ t, s_seq (t + 1) = step n m L (s_seq t) (coefficients_schedule gamma K t).1 (coefficients_schedule gamma K t).2) :
  ∀ t : ℕ, (s_seq (t + 1)).z = (s_seq t).z - (1 / (K * Real.sqrt ((t : ℝ) + gamma))) • F_operator n m L (s_seq t).z + (gamma / ((t : ℝ) + gamma)) • (z_init - (s_seq t).z) := by
  intro t
  have hz0 := z0_eq n m L gamma K s_seq z_init h_init h_step t
  rw [h_step]
  have h_step_def : (step n m L (s_seq t) (coefficients_schedule gamma K t).1 (coefficients_schedule gamma K t).2).z =
    (s_seq t).z - (coefficients_schedule gamma K t).1 • F_operator n m L (s_seq t).z + (coefficients_schedule gamma K t).2 • ((s_seq t).z0 - (s_seq t).z) := rfl
  rw [h_step_def, hz0]
  rfl

lemma norm_convex_comb_sq (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (u v : E) (beta : ℝ) (h1 : 0 ≤ beta) (h2 : beta ≤ 1) :
  ‖(1 - beta) • u + beta • v‖^2 ≤ (1 - beta) * ‖u‖^2 + beta * ‖v‖^2 := by
  have h3 : 2 * inner ℝ u v ≤ ‖u‖^2 + ‖v‖^2 := by linarith[norm_sub_sq_real @u v▸sq_nonneg _,2]
  exact (pow_le_pow_left₀ (by. (bound)) (norm_add_le _ _) _).trans (.trans (by rw [norm_smul_of_nonneg ↑(sub_nonneg_of_le h2),norm_smul_of_nonneg h1]) (by ·linear_combination h2 *beta*(norm v -norm (u) ) ^2))

lemma inner_cross_bound (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (v G : E) (alpha beta : ℝ) :
  -2 * alpha * beta * inner ℝ v G ≤ 2 * beta^2 * ‖v‖^2 + 0.5 * alpha^2 * ‖G‖^2 := by
  have h1 : -4 * alpha * beta * inner ℝ v G ≤ 4 * beta^2 * ‖v‖^2 + alpha^2 * ‖G‖^2 := by cases le_total 0 (alpha*beta) with nlinarith[pow_three (2 *beta*norm v+alpha*norm G),pow_three (2 *beta*norm v-alpha*norm G),abs_le.1 (abs_real_inner_le_norm v G)]
  linarith

lemma one_step_bound (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (z z_star z_init G : E) (alpha beta K : ℝ)
  (h_alpha_nonneg : 0 ≤ alpha)
  (h_beta_nonneg : 0 ≤ beta) (h_beta_le_one : beta ≤ 1)
  (h_inner : 0 ≤ inner ℝ G (z - z_star))
  (h_G_bound : ‖G‖ ≤ K * ‖z - z_star‖)
  (z_next : E) (h_z_next : z_next - z_star = (1 - beta) • (z - z_star) + beta • (z_init - z_star) - alpha • G) :
  ‖z_next - z_star‖^2 ≤ (1 - beta + 1.5 * alpha^2 * K^2) * ‖z - z_star‖^2 + (beta + 2 * beta^2) * ‖z_init - z_star‖^2 := by
  let u := z - z_star
  let v := z_init - z_star
  let w := (1 - beta) • u + beta • v
  have hw : z_next - z_star = w - alpha • G := by rw [h_z_next]
  have h_norm_next : ‖z_next - z_star‖^2 = ‖w‖^2 - 2 * inner ℝ w (alpha • G) + ‖alpha • G‖^2 := by rw [←norm_sub_sq_real,hw]
  have h_inner_w_G : inner ℝ w (alpha • G) = alpha * (1 - beta) * inner ℝ u G + alpha * beta * inner ℝ v G := by zify[mul_comm alpha, add_mul,inner_add_left,inner_smul_left,inner_smul_right,w,mul_assoc]
                                                                                                                 try constructor
  have h_w_sq : ‖w‖^2 ≤ (1 - beta) * ‖u‖^2 + beta * ‖v‖^2 := norm_convex_comb_sq E u v beta h_beta_nonneg h_beta_le_one
  have h_alpha_G_sq : ‖alpha • G‖^2 = alpha^2 * ‖G‖^2 := by rwa [@norm_smul_of_nonneg, mul_pow]
  have h_cross := inner_cross_bound E v G alpha beta
  have h_inner_u_G : 0 ≤ 2 * alpha * (1 - beta) * inner ℝ u G := by exact real_inner_comm G u▸mul_nonneg (by push_cast[*, sub_nonneg, mul_nonneg, zero_le_two]) h_inner
  have h_G_sq : ‖G‖^2 ≤ K^2 * ‖u‖^2 := by exact (mul_pow K _ _)▸pow_le_pow_left₀ (norm_nonneg G) h_G_bound (2)
  linarith[mul_le_mul_of_nonneg_left h_G_sq<|sq_nonneg alpha]

lemma poly_bound (gamma t : ℝ) (h_t_nonneg : 0 ≤ t) (h_gamma : 2 ≤ gamma) :
  18 * (t + gamma) + 2 * gamma^2 ≤ 11 * gamma * (t + gamma) := by
  have h1 : 18 * (t + gamma) + 2 * gamma^2 = 18 * t + 18 * gamma + 2 * gamma^2 := by ring
  have h2 : 18 * t + 18 * gamma + 2 * gamma^2 ≤ 11 * gamma * t + 9 * gamma * gamma + 2 * gamma^2 := by nlinarith
  have h3 : 11 * gamma * t + 9 * gamma * gamma + 2 * gamma^2 = 11 * gamma * (t + gamma) := by ring
  linarith

lemma seq_bound_algebra_new (D0 D_t gamma t : ℝ)
  (h_D0 : 0 ≤ D0) (h_Dt_nonneg : 0 ≤ D_t) (h_Dt : D_t ≤ 12 * D0)
  (h_t_nonneg : 0 ≤ t) (h_gamma : 2 ≤ gamma) :
  let beta := gamma / (t + gamma)
  let alpha_K_sq := 1 / (t + gamma)
  (1 - beta + 1.5 * alpha_K_sq) * D_t + (beta + 2 * beta^2) * D0 ≤ 12 * D0 := by
  intro beta alpha_K_sq
  have h_tg_pos : 0 < t + gamma := by linarith
  have h_poly := poly_bound gamma t h_t_nonneg h_gamma
  have h_coef_nonneg : 0 ≤ 1 - beta + 1.5 * alpha_K_sq := by linear_combination 1.5*inv_pos.mpr (by assumption)+h_t_nonneg/(t+gamma)+div_self h_tg_pos.ne'
  have h_bound1 : (1 - beta + 1.5 * alpha_K_sq) * D_t ≤ (1 - beta + 1.5 * alpha_K_sq) * (12 * D0) :=
    mul_le_mul_of_nonneg_left h_Dt h_coef_nonneg
  have h_bound2 : (1 - beta + 1.5 * alpha_K_sq) * (12 * D0) + (beta + 2 * beta^2) * D0 ≤ 12 * D0 := by
    have h_sub : (1 - beta + 1.5 * alpha_K_sq) * 12 + (beta + 2 * beta^2) - 12 = -11 * beta + 18 * alpha_K_sq + 2 * beta^2 := by ring
    have h_core : -11 * beta + 18 * alpha_K_sq + 2 * beta^2 ≤ 0 := by
      have h_mul : (-11 * beta + 18 * alpha_K_sq + 2 * beta^2) * (t + gamma)^2 = -11 * gamma * (t + gamma) + 18 * (t + gamma) + 2 * gamma^2 := by push_cast only [beta, alpha_K_sq, add_mul,mul_one_div,neg_mul,div_mul_cancel₀ (@ _) h_tg_pos.ne', ←mul_assoc,sq]
                                                                                                                                                  field_simp[←add_mul,mul_assoc]
      have h_le_zero : -11 * gamma * (t + gamma) + 18 * (t + gamma) + 2 * gamma^2 ≤ 0 := by linarith [h_poly]
      exact (nonpos_of_mul_nonpos_left) (h_mul▸h_le_zero) (pow_pos (by assumption') _)
    linear_combination(h_core).trans' (h_sub).le *D0
  linarith

lemma bounded_iterates_D
  (n m : ℕ) (L : Z_space n m → ℝ)
  (h_diff : Differentiable ℝ L)
  (h_monotone : ∀ z w : Z_space n m, inner ℝ (F_operator n m L z - F_operator n m L w) (z - w) ≥ (0 : ℝ))
  (K : NNReal) (h_K_nonneg : 0 < K)
  (h_lipschitz : ∀ z w : Z_space n m, ‖F_operator n m L z - F_operator n m L w‖ ≤ K * ‖z - w‖)
  (gamma : ℝ) (h_gamma : 2 ≤ gamma)
  (s_seq : ℕ → State n m) (z_init z_star : Z_space n m)
  (h_init : s_seq 0 = { z := z_init, z0 := z_init, t := 0, history := [z_init]})
  (h_step : ∀ t, s_seq (t + 1) = step n m L (s_seq t) (coefficients_schedule gamma K t).1 (coefficients_schedule gamma K t).2)
  (h_saddle : IsSaddlePoint n m L z_star)
  (h_opt : F_operator n m L z_star = 0) :
  ∀ t, ‖(s_seq t).z - z_star‖^2 ≤ 12 * ‖z_init - z_star‖^2 := by
  intro t
  induction t with
  | zero =>
    have h0 : (s_seq 0).z = z_init := by rw [h_init]
    rw [h0]
    have : 0 ≤ ‖z_init - z_star‖^2 := sq_nonneg _
    linarith
  | succ t ih =>
    have hz_update := z_update_eq n m L gamma K s_seq z_init h_init h_step t
    let alpha := 1 / (K * Real.sqrt (t + gamma))
    let beta := gamma / (t + gamma)
    have h_alpha_nonneg : 0 ≤ alpha := by iterate ·positivity
    have h_beta_nonneg : 0 ≤ beta := by {positivity}
    have h_beta_le_one : beta ≤ 1 := by repeat·bound [zero_le_two.trans (h_gamma)]
    have h_inner : 0 ≤ inner ℝ (F_operator n m L (s_seq t).z) ((s_seq t).z - z_star) := inner_F_operator_self_ge_zero n m L h_monotone z_star h_opt ((s_seq t).z)
    have h_G_bound : ‖F_operator n m L (s_seq t).z‖ ≤ K * ‖(s_seq t).z - z_star‖ := F_operator_lipschitz_bound n m L K h_lipschitz z_star h_opt ((s_seq t).z)
    have hz_next : (s_seq (t + 1)).z - z_star = (1 - beta) • ((s_seq t).z - z_star) + beta • (z_init - z_star) - alpha • F_operator n m L (s_seq t).z := by exact hz_update▸by module
    have h_one_step := one_step_bound (Z_space n m) ((s_seq t).z) z_star z_init (F_operator n m L (s_seq t).z) alpha beta K h_alpha_nonneg h_beta_nonneg h_beta_le_one h_inner h_G_bound ((s_seq (t + 1)).z) hz_next
    let D0 := ‖z_init - z_star‖^2
    let D_t := ‖(s_seq t).z - z_star‖^2
    have h_alpha_sq : alpha^2 * K^2 = 1 / (t + gamma) := by rw [←eq_div_iff (by ·positivity), one_div_pow, mul_pow _,Real.sq_sqrt (by positivity),div_div, mul_comm]
    have h_bound_algebra := seq_bound_algebra_new D0 D_t gamma t (sq_nonneg _) (sq_nonneg _) ih (by positivity) h_gamma
    use h_one_step.trans (by rwa[mul_assoc 1.5,h_alpha_sq])

lemma bounded_iterates_D_exist_helper (D_star D0 D : ℝ) (h_star : D_star ≤ 12 * D0)
  (h_D : D = (Real.sqrt 12 + 1) * Real.sqrt D0) (h_D0 : 0 ≤ D0) (h_star_nonneg : 0 ≤ D_star) :
  Real.sqrt D_star + Real.sqrt D0 ≤ D := by
  linear_combination Real.sqrt_le_sqrt ↑h_star-h_D+.sqrt_mul' ↑12 ↑h_D0

lemma bounded_iterates_D_exist
  (n m : ℕ) (L : Z_space n m → ℝ)
  (h_diff : Differentiable ℝ L)
  (h_monotone : ∀ z w : Z_space n m, inner ℝ (F_operator n m L z - F_operator n m L w) (z - w) ≥ (0 : ℝ))
  (K : NNReal) (h_K_nonneg : 0 < K)
  (h_lipschitz : ∀ z w : Z_space n m, ‖F_operator n m L z - F_operator n m L w‖ ≤ K * ‖z - w‖)
  (gamma : ℝ) (h_gamma : 2 ≤ gamma)
  (s_seq : ℕ → State n m) (z_init : Z_space n m)
  (h_init : s_seq 0 = { z := z_init, z0 := z_init, t := 0, history := [z_init]})
  (h_step : ∀ t, s_seq (t + 1) = step n m L (s_seq t) (coefficients_schedule gamma K t).1 (coefficients_schedule gamma K t).2)
  (z_star : Z_space n m) (h_saddle : IsSaddlePoint n m L z_star) (h_opt : F_operator n m L z_star = 0) :
  ∃ D : ℝ, 0 ≤ D ∧ ∀ t, ‖(s_seq t).z - z_init‖ ≤ D := by
  have h_bound := bounded_iterates_D n m L h_diff h_monotone K h_K_nonneg h_lipschitz gamma h_gamma s_seq z_init z_star h_init h_step h_saddle h_opt
  use (Real.sqrt 12 + 1) * ‖z_init - z_star‖
  constructor
  · have h_pos1 : 0 ≤ Real.sqrt 12 + 1 := by positivity
    have h_pos2 : 0 ≤ ‖z_init - z_star‖ := norm_nonneg _
    positivity
  · intro t
    have h_tri : ‖(s_seq t).z - z_init‖ ≤ ‖(s_seq t).z - z_star‖ + ‖z_init - z_star‖ := by
      have h_eq : (s_seq t).z - z_init = ((s_seq t).z - z_star) + (z_star - z_init) := by abel
      rw [h_eq]
      have h_tri2 := norm_add_le ((s_seq t).z - z_star) (z_star - z_init)
      have h_symm : ‖z_star - z_init‖ = ‖z_init - z_star‖ := norm_sub_rev _ _
      rw [h_symm] at h_tri2
      exact h_tri2
    have h_D_bound := h_bound t
    have h_sqrt : Real.sqrt (‖(s_seq t).z - z_star‖^2) ≤ Real.sqrt (12 * ‖z_init - z_star‖^2) := Real.sqrt_le_sqrt h_D_bound
    rw [Real.sqrt_sq (norm_nonneg _)] at h_sqrt
    have h_sqrt2 : Real.sqrt (12 * ‖z_init - z_star‖^2) = Real.sqrt 12 * ‖z_init - z_star‖ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
    rw [h_sqrt2] at h_sqrt
    linarith

lemma A_bound (t gamma : ℝ) (ht : 0 ≤ t) (hgamma : 0 < gamma) :
  let a1 := 1 / Real.sqrt (t + 1 + gamma)
  let a0 := 1 / Real.sqrt (t + gamma)
  let b1 := gamma / (t + 1 + gamma)
  1 - b1 - (a0 - a1) / a0 ≤ 1 - gamma / (t + 1 + gamma) - 0.5 / (t + 1 + gamma) := by field_simp [hgamma]
                                                                                      nlinarith[pow_three ((t+gamma).sqrt-(t+1+gamma).sqrt),(t+gamma).sq_sqrt (by bound),(t+1+gamma).sq_sqrt (by bound),(t+1+gamma).sqrt_pos_of_pos (by bound)]

lemma error_term_bound (t gamma : ℝ) (ht : 0 ≤ t) (hgamma : 1 ≤ gamma) :
  let a1 := 1 / Real.sqrt (t + 1 + gamma)
  let a0 := 1 / Real.sqrt (t + gamma)
  let b1 := gamma / (t + 1 + gamma)
  let b0 := gamma / (t + gamma)
  |((a0 - a1) / a0) * b0 + b1 - b0| ≤ gamma / (t + gamma)^2 := by
    norm_num[div_eq_mul_inv, sub_mul,mul_comm, mul_sub,mul_left_comm, add_nonneg _,ht,mul_assoc,abs_le,mt hgamma.trans_eq]
    field_simp
    use (by nlinarith[pow_three ((t+gamma).sqrt-(t+1+gamma).sqrt),pow_three (t+gamma),(t+gamma).sq_sqrt (by bound),(t+1+gamma).sq_sqrt (by bound),(t+1+gamma).sqrt_nonneg])
    nlinarith[pow_three (t+gamma),(t+gamma).sqrt_le_iff.1 (refl _),(t+1+gamma).sq_sqrt (by linarith),(t+1+gamma).sqrt_nonneg,mul_nonneg (t+gamma).sqrt_nonneg (by linarith:0≤gamma+t)]

lemma contraction_factor_sq (x gamma : ℝ) (hx : 0 ≤ x) (hx_le : x ≤ 1 / (1 + gamma)) (hg : 2 ≤ gamma) :
  (1 - gamma * x - 0.5 * x)^2 + x ≤ (1 - 1.15 * x)^2 := by nlinarith only [hx, mul_le_mul_of_nonneg_right hg hx,(le_div_iff₀ (by(((linear_combination hg))))).mp ↑hx_le]

lemma delta_contraction_factor (t gamma : ℝ) (ht : 1 ≤ t) (hgamma : 2 ≤ gamma) (K : ℝ) (hK : 0 < K) :
  let a1_K := 1 / Real.sqrt (t + 1 + gamma)
  let a0_K := 1 / Real.sqrt (t + gamma)
  let b1 := gamma / (t + 1 + gamma)
  let A := 1 - b1 - (a0_K - a1_K) / a0_K
  let a1 := a1_K / K
  0 ≤ A ∧ Real.sqrt (A^2 + a1^2 * K^2) ≤ 1 - 1.15 / (t + 1 + gamma) := by
    norm_num[ht.trans',hgamma.trans',div_pow, sub_div, add_nonneg, add_eq_zero_iff_of_nonneg _,hK.ne']
    field_simp
    use (by nlinarith[pow_three ((t+1+gamma).sqrt-(t+gamma).sqrt),(t+1+gamma).sq_sqrt (by bound),Real.sqrt_le_iff.1 <|refl (t+gamma).sqrt]),(le_div_iff₀ (by bound)).1 ?_
    rw[add_sub_cancel_right,Real.sq_sqrt (by bound),←sq_le_sq₀ (by bound) (by linarith),mul_pow,Real.sq_sqrt (by bound),mul_div, mul_div_mul_left _ _ (by nlinarith)]
    have:=sq_nonneg<|(t+1+gamma).sqrt -(t +gamma).sqrt
    norm_num[ht.trans',hgamma.trans',div_le_iff₀, sub_sq, mul_pow, add_pos_of_pos_of_nonneg] at this⊢
    norm_num[mul_assoc, sub_div, mul_sub, add_div, mul_div_assoc,sq,ne_of_gt, add_pos _,ht.trans_lt',hgamma.trans_lt',le_of_lt]at*
    nlinarith[Real.sqrt_le_iff.1 ((t+1+gamma).sqrt_mul (by bound) (t+gamma)).le,(t+1+gamma).sq_sqrt (by bound),mul_le_mul_of_nonneg_left hgamma (sub_nonneg.2 ht)]

lemma delta_algebra_subst (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (z2 z1 z0 z_init G1 G0 : E)
  (a1 a0 b1 b0 : ℝ)
  (h1 : z2 = z1 - a1 • G1 + b1 • (z_init - z1))
  (h0 : z1 = z0 - a0 • G0 + b0 • (z_init - z0))
  (ha0 : a0 ≠ 0) :
  z2 - z1 = (1 - b1 - (a0 - a1) / a0) • (z1 - z0) - a1 • (G1 - G0) +
    (((a0 - a1) / a0) * b0 + b1 - b0) • (z_init - z0) := by push_cast only [smul_sub, true, *]
                                                            linear_combination(norm:=module)-(a0-a1) •div_self ha0 •G0

lemma delta_norm_bound (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (d1 d0 G_diff E_err : E) (A a1 K : ℝ)
  (hA_pos : 0 ≤ A) (ha1_pos : 0 ≤ a1)
  (hd1 : d1 = A • d0 - a1 • G_diff + E_err)
  (h_inner : 0 ≤ inner ℝ G_diff d0)
  (h_G : ‖G_diff‖ ≤ K * ‖d0‖) :
  ‖d1‖ ≤ Real.sqrt (A^2 + a1^2 * K^2) * ‖d0‖ + ‖E_err‖ := by
    use hd1▸norm_add_le_of_le ((le_of_sq_le_sq) (.trans (by rw [norm_sub_sq_real,norm_smul_of_nonneg (by valid),norm_smul_of_nonneg (by valid),real_inner_smul_right,real_inner_smul_left,real_inner_comm]) ? _) (by bound)) (refl _)
    linear_combination (2 *h_inner* A * a1)-(A^2+a1^2*K^2).sq_sqrt (by bound) *norm d0^2+a1^2*pow_le_pow_left₀ (by bound) h_G (2)

lemma delta_induction (gamma C : ℝ) (hgamma : 2 ≤ gamma) (d : ℕ → ℝ)
  (hd : ∀ t, 1 ≤ t → d (t + 1) ≤ (1 - 1.15 / ((t:ℝ) + 1 + gamma)) * d t + C / ((t:ℝ) + gamma)^2) :
  ∃ E, 0 ≤ E ∧ ∀ t, 1 ≤ t → d t ≤ E / ((t:ℝ) + gamma) := by
    norm_num only[sq, one_sub_div (by positivity: ( ↑(_ : ℕ) : ℝ)+1+gamma ≠0), ←div_div] at hd
    refine(exists_nat_ge (d (1)*(1+gamma)⊔20* C)).elim fun A B=>⟨max 0 A,le_sup_left,fun R L=>(le_div_iff₀ (by positivity)).2 ?_⟩
    use le_max_of_le_right ((1).le_induction (by push_cast[sup_le_iff.1 B]) ( fun and K V=>.trans (by rw [Nat.cast_succ]) ((le_div_iff₀ (by positivity)).1 ((hd and K).trans (.trans (by rw [mul_comm, mul_div]) ?_)))) R L)
    exact (le_sub_iff_add_le').1.comp (div_div _ _ _).trans_le (((div_le_div_iff₀ (by positivity) (by positivity)).2 (by nlinarith[pow_three (and+gamma-1), max_le_iff.1 B])).trans_eq<|sub_div _ _ _)

lemma bounded_differences_E
  (n m : ℕ) (L : Z_space n m → ℝ)
  (h_diff : Differentiable ℝ L)
  (h_monotone : ∀ z w : Z_space n m, inner ℝ (F_operator n m L z - F_operator n m L w) (z - w) ≥ (0 : ℝ))
  (K : NNReal) (h_K_nonneg : 0 < K)
  (h_lipschitz : ∀ z w : Z_space n m, ‖F_operator n m L z - F_operator n m L w‖ ≤ K * ‖z - w‖)
  (gamma : ℝ) (h_gamma : 2 ≤ gamma)
  (s_seq : ℕ → State n m) (z_init : Z_space n m)
  (h_init : s_seq 0 = { z := z_init, z0 := z_init, t := 0, history := [z_init]})
  (h_step : ∀ t, s_seq (t + 1) = step n m L (s_seq t) (coefficients_schedule gamma K t).1 (coefficients_schedule gamma K t).2)
  (z_star : Z_space n m) (h_saddle : IsSaddlePoint n m L z_star) (h_opt : F_operator n m L z_star = 0) :
  ∃ E : ℝ, 0 ≤ E ∧ ∀ t, 1 ≤ t → ‖(s_seq (t + 1)).z - (s_seq t).z‖ ≤ E / ((t : ℝ) + gamma) := by
  have h_bound_D := bounded_iterates_D_exist n m L h_diff h_monotone K h_K_nonneg h_lipschitz gamma h_gamma s_seq z_init h_init h_step z_star h_saddle h_opt
  rcases h_bound_D with ⟨D, hD_nonneg, hD⟩
  let C_bound := gamma * D
  have hd : ∀ t, 1 ≤ t → ‖(s_seq (t + 2)).z - (s_seq (t + 1)).z‖ ≤ (1 - 1.15 / ((t:ℝ) + 1 + gamma)) * ‖(s_seq (t + 1)).z - (s_seq t).z‖ + C_bound / ((t:ℝ) + gamma)^2 := by
    intro t ht
    let z2 := (s_seq (t + 2)).z
    let z1 := (s_seq (t + 1)).z
    let z0 := (s_seq t).z
    let G1 := F_operator n m L z1
    let G0 := F_operator n m L z0

    let a1_K := 1 / Real.sqrt ((t:ℝ) + 1 + gamma)
    let a0_K := 1 / Real.sqrt ((t:ℝ) + gamma)
    let b1 := gamma / ((t:ℝ) + 1 + gamma)
    let b0 := gamma / ((t:ℝ) + gamma)

    let a1 := a1_K / (K:ℝ)
    let a0 := a0_K / (K:ℝ)

    have h1 : z2 = z1 - a1 • G1 + b1 • (z_init - z1) := by
      simp_rw [z2,z1,G1,h_step (t+1),step]
      congr
      · norm_num[a1,a1_K,coefficients_schedule]
        rfl
      · use show(_, _).2 = _ by zify[b1]
      · use t.rec (by norm_num[step, *]) (by norm_num+contextual[step, *])
    have h0 : z1 = z0 - a0 • G0 + b0 • (z_init - z0) := by
      norm_num[step, G0,b0, a0,a0_K, false, z0, z1, *]
      clear h_diff h_monotone h_K_nonneg h_lipschitz h_saddle h_opt hD_nonneg hD C_bound a1_K a0_K b1 b0(a1)a0 h1 z2 z1 z0 G1 G0
      show _-(_, _).1 •_+(_, _).2 •_ = _
      norm_num[mul_comm, (by induction. with simp_all![step]:∀ (n : ℕ), (s_seq n).z0 =z_init),div_eq_mul_inv]
    have ha0 : a0 ≠ 0 := by repeat positivity

    let A := 1 - b1 - (a0_K - a1_K) / a0_K
    let E_err := (((a0_K - a1_K) / a0_K) * b0 + b1 - b0) • (z_init - z0)

    have h_subst : z2 - z1 = A • (z1 - z0) - a1 • (G1 - G0) + E_err := by use h1▸h0▸?_
                                                                          linear_combination(norm:=module)(a1_K-a0_K) •div_self (by positivity:a0_K≠0) •(K:ℝ)⁻¹ •G0

    have hK_pos : 0 < (K:ℝ) := NNReal.coe_pos.mpr h_K_nonneg
    have h_contract := delta_contraction_factor (t:ℝ) gamma (by exact_mod_cast ht) h_gamma (K:ℝ) hK_pos

    have h_inner : 0 ≤ inner ℝ (G1 - G0) (z1 - z0) := h_monotone z1 z0
    have h_G : ‖G1 - G0‖ ≤ (K:ℝ) * ‖z1 - z0‖ := h_lipschitz z1 z0

    have ha1_pos : 0 ≤ a1 := by apply div_nonneg (one_div_nonneg.2 (@ Real.sqrt_nonneg _)) (hK_pos).le
    have h_norm := delta_norm_bound (Z_space n m) (z2 - z1) (z1 - z0) (G1 - G0) E_err A a1 (K:ℝ) h_contract.1 ha1_pos h_subst h_inner h_G

    have h_err_coef : |(((a0_K - a1_K) / a0_K) * b0 + b1 - b0)| ≤ gamma / ((t:ℝ) + gamma)^2 := by
      clear h1 ha0 h_diff h_opt hD_nonneg hD C_bound ht h_lipschitz h_saddle h_K_nonneg
      norm_num[a1_K, sub_mul,b0, sub_add, sub_div, add_nonneg _,b1,a0_K,h_gamma.trans_lt',abs_of_nonneg,ne_of_gt, add_pos_of_nonneg_of_pos _,div_mul_div_comm _,sq]
      field_simp[abs_of_neg,div_le_iff₀]
      rw[abs_div,abs_mul,abs_of_nonneg (by bound),abs_of_neg ∘sub_neg.2,abs_of_nonneg (by bound),mul_div,div_le_iff₀ (by positivity)]
      · field_simp[mul_comm gamma,←mul_assoc]
        linear_combination(t+gamma+1)*(t+gamma) *.sqrt_le_sqrt (by linear_combination:t+gamma≤t+1+gamma)+.sqrt_nonneg _
      · exact (lt_of_abs_lt (abs_lt_of_sq_lt_sq (lt_of_le_of_lt (by rw [mul_pow,Real.sq_sqrt (by positivity)]) (by nlinarith only[h_gamma,(t+gamma).sq_sqrt (by positivity)])) (by positivity)))
    have hz0_bound : ‖z_init - z0‖ ≤ D := by
      have h := hD t
      rw [norm_sub_rev]
      exact h
    have h_err_norm : ‖E_err‖ ≤ C_bound / ((t:ℝ) + gamma)^2 := by
      clear h1 ha0(h_diff)h_monotone h_K_nonneg h_lipschitz h_init h_step h_opt hD_nonneg(hD)h_saddle hK_pos h_inner h_G
      exact (norm_smul _ _).trans_le.comp (mul_le_mul (by assumption) (by assumption) (norm_nonneg _) (by((((positivity)))))).trans (mul_right_comm _ _ _).le

    clear h1 ha0(h_diff) (h_opt) (hD_nonneg) (hD)h_monotone h_K_nonneg h_lipschitz h_saddle
    apply h_norm.trans (add_le_add ↑(mul_le_mul_of_nonneg_right h_contract.right <|norm_nonneg _) (by assumption ) )
  exact delta_induction gamma C_bound h_gamma (fun t => ‖(s_seq (t + 1)).z - (s_seq t).z‖) hd

lemma F_norm_bound_helper (E_space : Type*) [NormedAddCommGroup E_space] [NormedSpace ℝ E_space]
  (z_next z_curr z_init F : E_space) (alpha beta : ℝ)
  (h_eq : z_next = z_curr - alpha • F + beta • (z_init - z_curr))
  (h_alpha : 0 < alpha) (h_beta : 0 ≤ beta) :
  ‖F‖ ≤ (1 / alpha) * ‖z_curr - z_next‖ + (beta / alpha) * ‖z_init - z_curr‖ := by
  simp_all only [div_eq_inv_mul,mul_assoc, sub_sub_self,le_inv_mul_iff₀, sub_add, true,←mul_add]
  simp_all only[←norm_smul_of_nonneg, one_mul,le_of_lt,norm_le_norm_sub_add]

lemma rate_algebra (T : ℝ) (K gamma D E : ℝ) (hT : 1 ≤ T)
  (h_K : 0 < K) (h_gamma : 0 ≤ gamma) (h_D : 0 ≤ D) (h_E : 0 ≤ E)
  (F_norm z_diff z_dist : ℝ)
  (h_F : F_norm ≤ (K * Real.sqrt (T + gamma)) * z_diff + (K * gamma / Real.sqrt (T + gamma)) * z_dist)
  (h_diff : z_diff ≤ E / (T + gamma))
  (h_dist : z_dist ≤ D)
  (h_F_nonneg : 0 ≤ F_norm) :
  F_norm^2 ≤ ((K * E) / Real.sqrt (T + gamma) + (K * gamma * D) / Real.sqrt (T + gamma))^2 := by
  apply pow_le_pow_left₀ (by assumption) (h_F.trans (by·linear_combination K * (gamma/(T+gamma).sqrt * h_dist+(h_diff * ( T+gamma).sqrt+.sqrt_div_self * ( E)))))

lemma last_iterate_algebra_h1 (T gamma : ℝ) (hT : 1 ≤ T) (hgamma : 2 ≤ gamma) :
  Real.sqrt (T + gamma) / (T + 1) ≤ Real.sqrt (1 + gamma) / Real.sqrt T := by
  have h_T_pos : 0 < T := by linarith
  have h_sqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr h_T_pos
  have h_T1_pos : 0 < T + 1 := by linarith
  rw [div_le_div_iff₀ h_T1_pos h_sqrt_pos]
  have h_sq_le : (Real.sqrt (T + gamma) * Real.sqrt T) ^ 2 ≤ (Real.sqrt (1 + gamma) * (T + 1)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    have h_diff : (1 + gamma) * (T + 1)^2 - (T + gamma) * T =
      T^2 * gamma + T * (gamma + 2) + gamma + 1 := by ring
    have h_diff_pos : 0 ≤ T^2 * gamma + T * (gamma + 2) + gamma + 1 := by positivity
    linarith
  have h_nonneg1 : 0 ≤ Real.sqrt (T + gamma) * Real.sqrt T := by positivity
  have h_nonneg2 : 0 ≤ Real.sqrt (1 + gamma) * (T + 1) := by positivity
  have h_abs : |Real.sqrt (T + gamma) * Real.sqrt T| ≤ |Real.sqrt (1 + gamma) * (T + 1)| := sq_le_sq.mp h_sq_le
  rw [abs_of_nonneg h_nonneg1, abs_of_nonneg h_nonneg2] at h_abs
  exact h_abs

lemma last_iterate_algebra_h2 (T gamma : ℝ) (hT : 1 ≤ T) (hgamma : 2 ≤ gamma) :
  1 / Real.sqrt (T + gamma) ≤ 1 / Real.sqrt T := by
  have h_T_pos : 0 < T := by linarith
  have h_Tg_pos : 0 < T + gamma := by linarith
  have h_le : Real.sqrt T ≤ Real.sqrt (T + gamma) := by
    apply Real.sqrt_le_sqrt
    linarith
  have h_sqrt_T_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr h_T_pos
  have h_sqrt_Tg_pos : 0 < Real.sqrt (T + gamma) := Real.sqrt_pos.mpr h_Tg_pos
  exact one_div_le_one_div_of_le h_sqrt_T_pos h_le

lemma last_iterate_algebra (T K gamma D E : ℝ) (hT : 1 ≤ T) (hgamma : 2 ≤ gamma) (hK : 0 < K) (hD : 0 ≤ D) (hE : 0 ≤ E) :
  let C := (K * E + K * gamma * D) ^ 2 + 100
  (K * E / Real.sqrt (T + gamma) + K * gamma * D / Real.sqrt (T + gamma)) ^ 2 ≤ C / T := by
  have h_C : (K * E + K * gamma * D) ^ 2 ≤ (K * E + K * gamma * D) ^ 2 + 100 := by linarith
  exact (.trans (by rw [←add_div _,div_pow _,Real.sq_sqrt (by {positivity})]) (by bound [zero_le_two.trans hgamma]))


/--
The last-iterate convergence of Anchored Simultaneous Gradient Descent (SimGD-A)
with parameter $p = 1/2$.

This theorem corresponds to the critical boundary case of Theorem 3 in arXiv:1905.10899,
where the step size $\alpha_t$ and anchoring coefficient $\beta_t$ are set to achieve
an $O(1/T)$ convergence rate on the squared norm of the operator.

While Theorem 3 in the paper is formally stated for $p \in (1/2, 1)$, the "Further
discussion" in Section 4.2 identifies $p = 1/2$ as the theoretical limit of stability
and discretization.

A DeepMind prover agent was able to proof that convergence holds for $p = 1/2$.
-/
@[category research solved, AMS 49 90]
theorem last_iterate_convergence
  (L : (Z_space n m) → ℝ)
  (h_diff : Differentiable ℝ L)

  (h_monotone : ∀ z w : Z_space n m,
    inner ℝ (F_operator n m L z - F_operator n m L w) (z - w) ≥ (0 : ℝ)) -- Convex-Concave

  (K : NNReal) (h_K_nonneg : 0 < K) -- Lipschitz-Continuous
  (h_lipschitz : ∀ z w : Z_space n m,
    ‖F_operator n m L z - F_operator n m L w‖ ≤ K * ‖z - w‖)

  -- Algorithm Parameter
  (gamma : ℝ) (h_gamma : 2 ≤ gamma)

  -- Sequence generated by the algorithm
  (s_seq : ℕ → State n m)
  (z_init : Z_space n m)
  (h_init : s_seq 0 = { z := z_init, z0 := z_init, t := 0, history := [z_init]})
  (h_step : ∀ t, s_seq (t + 1) = step n m L (s_seq t) (coefficients_schedule gamma K t).1 (coefficients_schedule gamma K t).2)

  -- Saddle point existence
  (z_star : Z_space n m)
  (h_saddle : IsSaddlePoint n m L z_star)
  (h_opt : F_operator n m L z_star = 0) :

  -- Convergence Result: ‖G(z_T)‖^2 ≤ O(1 / T)
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 1 ≤ T →
    let s_T := s_seq T
    ‖F_operator n m L s_T.z‖ ^ 2 ≤ C / (T : ℝ) := by
  have h_bound_D := bounded_iterates_D_exist n m L h_diff h_monotone K h_K_nonneg h_lipschitz gamma h_gamma s_seq z_init h_init h_step z_star h_saddle h_opt
  have h_bound_E := bounded_differences_E n m L h_diff h_monotone K h_K_nonneg h_lipschitz gamma h_gamma s_seq z_init h_init h_step z_star h_saddle h_opt
  rcases h_bound_D with ⟨D, hD_nonneg, hD⟩
  rcases h_bound_E with ⟨E, hE_nonneg, hE⟩

  let C := ((K:ℝ) * E + (K:ℝ) * gamma * D)^2 + 100
  use C
  constructor
  · have h_pos : 0 ≤ ((K:ℝ) * E + (K:ℝ) * gamma * D)^2 := sq_nonneg _
    linarith
  · intro T hT
    have h_z_eq := z_update_eq n m L gamma (K:ℝ) s_seq z_init h_init h_step T
    have h_alpha_pos : 0 < 1 / ((K:ℝ) * Real.sqrt ((T : ℝ) + gamma)) := by classical positivity
    have h_beta_nonneg : 0 ≤ gamma / ((T : ℝ) + gamma) := by norm_num only[h_gamma.trans',div_nonneg, T.cast_nonneg, add_nonneg]

    have h_F_helper := F_norm_bound_helper (Z_space n m)
      (s_seq (T + 1)).z (s_seq T).z z_init (F_operator n m L (s_seq T).z)
      (1 / ((K:ℝ) * Real.sqrt ((T : ℝ) + gamma))) (gamma / ((T : ℝ) + gamma))
      h_z_eq h_alpha_pos h_beta_nonneg

    have h_alpha_inv : 1 / (1 / ((K:ℝ) * Real.sqrt ((T : ℝ) + gamma))) = (K:ℝ) * Real.sqrt ((T : ℝ) + gamma) := by apply one_div_one_div
    have h_beta_div_alpha : (gamma / ((T : ℝ) + gamma)) / (1 / ((K:ℝ) * Real.sqrt ((T : ℝ) + gamma))) = (K:ℝ) * gamma / Real.sqrt ((T : ℝ) + gamma) := by exact (div_div_div_eq _ _ _ _).trans (by linear_combination K*gamma*(T+gamma).sqrt_div_self)

    rw [h_alpha_inv, h_beta_div_alpha] at h_F_helper

    have hT_real : 1 ≤ (T : ℝ) := by repeat ·norm_cast
    have hgamma_nonneg : 0 ≤ gamma := by positivity
    have hz_diff : ‖(s_seq T).z - (s_seq (T + 1)).z‖ ≤ E / ((T : ℝ) + gamma) := by
      have h := hE T hT
      rw [norm_sub_rev] at h
      exact h
    have hz_dist : ‖z_init - (s_seq T).z‖ ≤ D := by
      have h := hD T
      rw [norm_sub_rev] at h
      exact h
    have hF_nonneg : 0 ≤ ‖F_operator n m L (s_seq T).z‖ := by focus apply @norm_nonneg
    have hK_pos : 0 < (K:ℝ) := by repeat assumption

    have h_F_norm_sq := rate_algebra (T:ℝ) (K:ℝ) gamma D E hT_real hK_pos hgamma_nonneg hD_nonneg hE_nonneg
      ‖F_operator n m L (s_seq T).z‖ ‖(s_seq T).z - (s_seq (T + 1)).z‖ ‖z_init - (s_seq T).z‖
      h_F_helper hz_diff hz_dist hF_nonneg

    have h_C_ge := last_iterate_algebra (T : ℝ) (K:ℝ) gamma D E hT_real h_gamma hK_pos hD_nonneg hE_nonneg
    exact le_trans h_F_norm_sq h_C_ge


noncomputable def coefficients_schedule_p
  (p gamma K : ℝ)
  (t : ℕ) : ℝ × ℝ :=
  ((1 - p) / (K * Real.rpow ((t : ℝ) + 1) p), (1 - p) * gamma / ((t : ℝ) + 1))

/--
Divergence conjecture for $0 < p < 1/2$.

The paper states that for $p < 1/2$, the discrete method simulates the ODE poorly and
simple tests on bilinear examples show divergence. This open problem asks to show that
there exist convex-concave problems for which SimGD-A with $p \in (0, 1/2)$ does not
achieve an $O(1/T)$ convergence rate.
-/
@[category research open, AMS 49 90]
theorem divergence_for_p_lt_half
  (p : ℝ) (hp1 : 0 < p) (hp2 : p < 1/2)
  (gamma : ℝ) (h_gamma : 2 ≤ gamma) :
  ∃ (n' m' : ℕ) (L : Z_space n' m' → ℝ)
    (K : NNReal) (_ : 0 < K)
    (_ : Differentiable ℝ L)
    (_ : ∀ z w : Z_space n' m',
      inner ℝ (F_operator n' m' L z - F_operator n' m' L w) (z - w) ≥ (0 : ℝ))
    (_ : ∀ z w : Z_space n' m',
      ‖F_operator n' m' L z - F_operator n' m' L w‖ ≤ K * ‖z - w‖)
    (z_star : Z_space n' m')
    (_ : IsSaddlePoint n' m' L z_star)
    (_ : F_operator n' m' L z_star = 0)
    (s_seq : ℕ → State n' m') (z_init : Z_space n' m')
    (_ : s_seq 0 = { z := z_init, z0 := z_init, t := 0, history := [z_init]})
    (_ : ∀ t, s_seq (t + 1) = step n' m' L (s_seq t)
      (coefficients_schedule_p p gamma K t).1
      (coefficients_schedule_p p gamma K t).2),
  ¬ (∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 1 ≤ T →
    ‖F_operator n' m' L (s_seq T).z‖ ^ 2 ≤ C / (T : ℝ)) := by
  sorry


end Arxiv.«1905.10899»
