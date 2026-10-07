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

import AEGISOverlay.RHKreinDigammaLowerBoundV1
import AEGISOverlay.RHKreinDigammaMonotonicityV1

/-!
# Sharp tail for the quarter-line digamma series

With `T = t²/4` and `a = n + 1/4`, each omitted summand is
`1/(n+1) - 1/a + T/(a (a² + T))`.  The first part telescopes as before; the second dominates
`φ(a) - φ(a+1)` with `φ(a) = T/(2a² + T)`, because
`(2a²+T)(2a²+4a+2+T) - (4a+2) a (a²+T) = 6a³ + 4a² + 2aT + 2T + T² ≥ 0`.
Hence the truncation keeps `T/(2a_N² + T)` instead of dropping the whole positive tail.
AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false

namespace AEGIS.RHKreinDigammaSharpTailV1

open Filter Topology
open AEGIS.RHKreinDigammaLowerBoundV1
open AEGIS.RHKreinDigammaMonotonicityV1

/-- The telescoping profile of the positive tail. -/
noncomputable def phi (T x : ℝ) : ℝ := T / (2 * x ^ 2 + T)

theorem phi_step (T x : ℝ) (hT : 0 ≤ T) (hx : 0 < x) :
    phi T x - phi T (x + 1) ≤ T / (x * (x ^ 2 + T)) := by
  unfold phi
  have h1 : 0 < 2 * x ^ 2 + T := by positivity
  have h2 : 0 < 2 * (x + 1) ^ 2 + T := by positivity
  have h3 : 0 < x * (x ^ 2 + T) := by positivity
  rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (mul_pos h1 h2) h3]
  have key : 0 ≤ T * (6 * x ^ 3 + 4 * x ^ 2 + 2 * x * T + 2 * T + T ^ 2) := by positivity
  nlinarith [key]

theorem term_lower (t : ℝ) (N n : ℕ) (hN : N ≤ n) :
    -(3 / 4 : ℝ) * (1 + 1 / ((N : ℝ) + 1 / 4)) *
        (1 / ((n : ℝ) + 1 / 4) - 1 / ((n : ℝ) + 1 / 4 + 1)) +
      (phi (t ^ 2 / 4) ((n : ℝ) + 1 / 4) - phi (t ^ 2 / 4) ((n : ℝ) + 1 / 4 + 1)) ≤
        quarterTerm t n := by
  set x : ℝ := (n : ℝ) + 1 / 4 with hxdef
  set q : ℝ := (N : ℝ) + 1 / 4 with hqdef
  set T : ℝ := t ^ 2 / 4 with hTdef
  have hT : 0 ≤ T := by rw [hTdef]; positivity
  have hx : 0 < x := by rw [hxdef]; positivity
  have hq : 0 < q := by rw [hqdef]; positivity
  have hqx : q ≤ x := by
    rw [hqdef, hxdef]; have : (N : ℝ) ≤ n := Nat.cast_le.mpr hN; linarith
  have hn1 : x ≤ (n : ℝ) + 1 := by rw [hxdef]; linarith
  have hphi := phi_step T x hT hx
  -- positive part
  have hpos : T / (x * (x ^ 2 + T)) = 1 / x - x / (x ^ 2 + T) := by
    field_simp; ring
  -- negative part
  have hneg : -(3 / 4 : ℝ) * (1 + 1 / q) * (1 / x - 1 / (x + 1)) ≤ 1 / ((n : ℝ) + 1) - 1 / x := by
    have hx1 : 0 < x + 1 := by linarith
    have hn : 0 < (n : ℝ) + 1 := by linarith
    have e1 : (1 + 1 / q) * (1 / x - 1 / (x + 1)) = (q + 1) / (q * (x * (x + 1))) := by
      field_simp; ring
    -- 1/(n+1) - 1/x = -(3/4)/((n+1) x) ≥ -(3/4)/x² ≥ -(3/4)(q+1)/(q x (x+1))
    have e3 : 1 / ((n : ℝ) + 1) - 1 / x = -(3 / 4) / (((n : ℝ) + 1) * x) := by
      rw [hxdef]; field_simp; ring
    rw [e3, mul_assoc, e1]
    have hA : (3 / 4) / (((n : ℝ) + 1) * x) ≤ (3 / 4) / (x * x) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos hx hx) (mul_le_mul_of_nonneg_right hn1 hx.le)
    have hB : (3 / 4) / (x * x) ≤ (3 / 4) * ((q + 1) / (q * (x * (x + 1)))) := by
      rw [← mul_div_assoc, div_le_div_iff₀ (mul_pos hx hx) (mul_pos hq (mul_pos hx hx1))]
      nlinarith [mul_nonneg (mul_nonneg hx.le hx.le) (sub_nonneg.mpr hqx)]
    rw [neg_div, neg_mul]
    linarith
  have hqt : quarterTerm t n = (1 / ((n : ℝ) + 1) - 1 / x) + (1 / x - x / (x ^ 2 + T)) := by
    simp only [quarterTerm, hxdef, hTdef]; ring
  rw [hqt, ← hpos]
  linarith

theorem partial_lower (t : ℝ) (N k : ℕ) :
    (∑ n ∈ Finset.range N, quarterTerm t n) -
        (3 / 4 : ℝ) * (1 + 1 / ((N : ℝ) + 1 / 4)) *
          (1 / ((N : ℝ) + 1 / 4) - 1 / (((N + k : ℕ) : ℝ) + 1 / 4)) +
        (phi (t ^ 2 / 4) ((N : ℝ) + 1 / 4) - phi (t ^ 2 / 4) (((N + k : ℕ) : ℝ) + 1 / 4)) ≤
      ∑ n ∈ Finset.range (N + k), quarterTerm t n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ht := term_lower t N (N + k) (by omega)
    rw [Nat.add_succ, Finset.sum_range_succ]
    have e : (((N + k).succ : ℕ) : ℝ) + 1 / 4 = (((N + k : ℕ) : ℝ) + 1 / 4) + 1 := by
      push_cast; ring
    rw [e]
    linarith

theorem tendsto_inv_shift (N : ℕ) :
    Tendsto (fun k : ℕ => 1 / (((N + k : ℕ) : ℝ) + 1 / 4)) atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => (((N + k : ℕ) : ℝ) + 1 / 4)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have h2 := h.inv_tendsto_atTop
  refine h2.congr (fun k => ?_)
  simp [one_div]

theorem tendsto_phi_shift (T : ℝ) (hT : 0 ≤ T) (N : ℕ) :
    Tendsto (fun k : ℕ => phi T (((N + k : ℕ) : ℝ) + 1 / 4)) atTop (𝓝 0) := by
  have hy : Tendsto (fun k : ℕ => (((N + k : ℕ) : ℝ) + 1 / 4)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have h : Tendsto (fun k : ℕ => 2 * ((((N + k : ℕ) : ℝ) + 1 / 4)) ^ 2 + T) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) (hy.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have hy4 : (1 / 4 : ℝ) ≤ ((N + k : ℕ) : ℝ) + 1 / 4 := by
      linarith [(Nat.cast_nonneg (N + k) : (0 : ℝ) ≤ ((N + k : ℕ) : ℝ))]
    nlinarith
  exact tendsto_const_nhds.div_atTop h

/-- Sharp lower bound with the true Euler constant. -/
theorem digamma_quarter_sharp_lower (t : ℝ) (N : ℕ) :
    -Real.eulerMascheroniConstant + (∑ n ∈ Finset.range N, quarterTerm t n) -
        (3 / 4 : ℝ) * (1 / ((N : ℝ) + 1 / 4) + 1 / ((N : ℝ) + 1 / 4) ^ 2) +
        (t ^ 2 / 4) / (2 * ((N : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4) ≤
      (Complex.digamma (quarterPoint t)).re := by
  have hT : (0 : ℝ) ≤ t ^ 2 / 4 := by positivity
  have hshift : Tendsto (fun k : ℕ => N + k) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop b] with k hk
    omega
  have hsum := (quarterTerm_hasSum t).tendsto_sum_nat.comp hshift
  have hlow : Tendsto (fun k : ℕ =>
      (∑ n ∈ Finset.range N, quarterTerm t n) -
        (3 / 4 : ℝ) * (1 + 1 / ((N : ℝ) + 1 / 4)) *
          (1 / ((N : ℝ) + 1 / 4) - 1 / (((N + k : ℕ) : ℝ) + 1 / 4)) +
        (phi (t ^ 2 / 4) ((N : ℝ) + 1 / 4) - phi (t ^ 2 / 4) (((N + k : ℕ) : ℝ) + 1 / 4)))
      atTop (𝓝 ((∑ n ∈ Finset.range N, quarterTerm t n) -
        (3 / 4 : ℝ) * (1 + 1 / ((N : ℝ) + 1 / 4)) * (1 / ((N : ℝ) + 1 / 4) - 0) +
        (phi (t ^ 2 / 4) ((N : ℝ) + 1 / 4) - 0))) := by
    refine (tendsto_const_nhds.sub (tendsto_const_nhds.mul
      (tendsto_const_nhds.sub (tendsto_inv_shift N)))).add
      (tendsto_const_nhds.sub (tendsto_phi_shift _ hT N))
  have h := le_of_tendsto_of_tendsto hlow hsum (Eventually.of_forall fun k => partial_lower t N k)
  have hq : (0 : ℝ) < (N : ℝ) + 1 / 4 := by positivity
  have heq : (3 / 4 : ℝ) * (1 + 1 / ((N : ℝ) + 1 / 4)) * (1 / ((N : ℝ) + 1 / 4) - 0) =
      (3 / 4 : ℝ) * (1 / ((N : ℝ) + 1 / 4) + 1 / ((N : ℝ) + 1 / 4) ^ 2) := by
    rw [sub_zero]; field_simp
  rw [heq] at h
  simp only [phi, sub_zero] at h
  linarith

end AEGIS.RHKreinDigammaSharpTailV1

#print axioms AEGIS.RHKreinDigammaSharpTailV1.digamma_quarter_sharp_lower
