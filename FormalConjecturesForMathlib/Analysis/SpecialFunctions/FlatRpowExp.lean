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

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

noncomputable section

open Filter Function Topology

namespace ContDiff

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A smooth function on the punctured space whose every iterated derivative is little-oh of the
distance to the origin extends smoothly across the origin, with zero Taylor series there. -/
theorem at_zero_of_iteratedFDeriv_isLittleO {f : E → F}
    (hf : ∀ x ≠ 0, ContDiffAt 𝕜 ∞ f x) (hzero : f 0 = 0)
    (hflat : ∀ m : ℕ, (iteratedFDeriv 𝕜 m f) =o[𝓝[≠] 0] (id : E → E)) :
    ContDiffAt 𝕜 ∞ f 0 := by
  classical
  let p : E → FormalMultilinearSeries 𝕜 E F := fun x m ↦
    if x = 0 then 0 else iteratedFDeriv 𝕜 m f x
  have hp_flat (m : ℕ) : (fun x ↦ p x m) =o[𝓝 0] (id : E → E) := by
    have heq : iteratedFDeriv 𝕜 m f =ᶠ[𝓝[≠] 0] fun x ↦ p x m := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
      simp [p, hx]
    rw [← nhdsNE_sup_pure (0 : E)]
    refine ((hflat m).congr' heq EventuallyEq.rfl).sup <|
      Asymptotics.isLittleO_iff.2 fun c hc ↦ ?_
    rw [eventually_pure]
    simp [p]
  have hp_deriv (m : ℕ) (x : E) :
      HasFDerivAt (p · m) (p x m.succ).curryLeft x := by
    by_cases hx : x = 0
    · subst x
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      have hfun : (fun h : E ↦ p h m - p 0 m - (p 0 m.succ).curryLeft h) =
          fun h ↦ p h m := by
        funext h
        have hp0 (i : ℕ) : p 0 i = 0 := by simp [p]
        rw [hp0 m, hp0 m.succ]
        have hz : (0 : ContinuousMultilinearMap 𝕜 (fun _ : Fin (m + 1) ↦ E) F).curryLeft h =
            0 := by
          ext v
          rfl
        rw [hz, sub_zero, sub_zero]
      simp only [zero_add]
      rw [hfun]
      exact hp_flat m
    · have heq (i : ℕ) : (fun y ↦ p y i) =ᶠ[𝓝 x] iteratedFDeriv 𝕜 i f := by
        filter_upwards [eventually_ne_nhds hx] with y hy
        simp [p, hy]
      have hd := ((hf x hx).differentiableAt_iteratedFDeriv (m := m)
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m)).hasFDerivAt
      rw [fderiv_iteratedFDeriv, Function.comp_apply] at hd
      refine (hd.congr_of_eventuallyEq (heq m)).congr_fderiv ?_
      simp only [p, hx, if_false, Nat.succ_eq_add_one]
      rfl
  have hp : HasFTaylorSeriesUpToOn ∞ f p Set.univ := by
    rw [hasFTaylorSeriesUpToOn_top_iff' le_rfl]
    constructor
    · intro x _
      by_cases hx : x = 0
      · subst x
        simp [p, hzero]
      · simp [p, hx]
    · intro m x _
      simpa only [hasFDerivWithinAt_univ] using hp_deriv m x
  exact hp.contDiffOn.contDiffAt univ_mem

/-- A smooth function with zero Taylor series at the origin is little-oh of every power of the
distance to the origin. -/
theorem isLittleO_norm_pow_of_iteratedFDeriv_zero [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ m : ℕ, iteratedFDeriv ℝ m f 0 = 0) (m n : ℕ) :
    iteratedFDeriv ℝ m f =o[𝓝 0] fun x ↦ ‖x‖ ^ n := by
  induction n generalizing m with
  | zero =>
      rw [show (fun x : E ↦ ‖x‖ ^ 0) = fun _ ↦ (1 : ℝ) by simp]
      rw [Asymptotics.isLittleO_one_iff]
      rw [← hzero m]
      exact hf.continuous_iteratedFDeriv (m := m)
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.continuousAt
  | succ n ih =>
      have hdiff : Differentiable ℝ (iteratedFDeriv ℝ m f) :=
        hf.differentiable_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m)
      have hderiv : fderiv ℝ (iteratedFDeriv ℝ m f) =o[𝓝 0] fun x ↦ ‖x‖ ^ n := by
        rw [Asymptotics.isLittleO_iff] at ⊢
        intro c hc
        filter_upwards [(ih (m + 1)).bound hc] with x hx
        rw [norm_fderiv_iteratedFDeriv]
        exact hx
      have h := (convex_univ : Convex ℝ (Set.univ : Set E)).isLittleO_pow_succ
        (Set.mem_univ 0) (fun x _ ↦ hdiff.differentiableAt.hasFDerivAt.hasFDerivWithinAt)
        (by simpa using hderiv)
      simpa [hzero m] using h

/-- Composing on the right preserves a zero Taylor series at the origin, provided the inner
function fixes the origin. -/
theorem iteratedFDeriv_comp_zero_of_outer [NormedSpace ℝ E] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : F → G} {f : E → F}
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0)
    (hzero : ∀ m : ℕ, iteratedFDeriv ℝ m g 0 = 0) (n : ℕ) :
    iteratedFDeriv ℝ n (g ∘ f) 0 = 0 := by
  let D := 1 + ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i f 0‖
  rw [← norm_eq_zero]
  apply le_antisymm
  · refine (norm_iteratedFDeriv_comp_le hg hf (mod_cast le_top) 0
      (C := 0) (D := D) ?_ ?_).trans ?_
    · intro i hi
      rw [hf0, hzero i]
      simp only [norm_zero]
      exact le_rfl
    · intro i hi hin
      have hD_one : 1 ≤ D := by
        simp only [D, le_add_iff_nonneg_right]
        exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
      calc
        ‖iteratedFDeriv ℝ i f 0‖ ≤ D := by
          simp only [D]
          exact le_add_of_nonneg_of_le zero_le_one <|
            Finset.single_le_sum (f := fun j ↦ ‖iteratedFDeriv ℝ j f 0‖)
              (fun j _ ↦ norm_nonneg _)
              (Finset.mem_range.mpr (Nat.lt_succ_of_le hin))
        _ ≤ D ^ i := le_self_pow₀ hD_one (Nat.ne_of_gt hi)
    · simp
  · exact norm_nonneg _

/-- Multiplying a smooth scalar-valued function with zero Taylor series by another smooth
function preserves its zero Taylor series. -/
theorem iteratedFDeriv_mul_zero_of_left [NormedSpace ℝ E] {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hzero : ∀ m : ℕ, iteratedFDeriv ℝ m f 0 = 0) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x ↦ f x * g x) 0 = 0 := by
  rw [← norm_eq_zero]
  apply le_antisymm
  · refine (norm_iteratedFDeriv_mul_le hf hg 0 (mod_cast le_top) (n := n)).trans ?_
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i]
    simp
  · exact norm_nonneg _

end ContDiff

namespace Real

/-- The extension by zero of `x ↦ exp (-c * x ^ (-a))` from the positive half-line. -/
def flatRpowExp (a c x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else exp (-c * x ^ (-a))

namespace flatRpowExp

theorem zero_of_nonpos (a c : ℝ) {x : ℝ} (hx : x ≤ 0) : flatRpowExp a c x = 0 := by
  simp [flatRpowExp, hx]

@[simp]
theorem zero (a c : ℝ) : flatRpowExp a c 0 = 0 := zero_of_nonpos a c le_rfl

theorem of_pos (a c : ℝ) {x : ℝ} (hx : 0 < x) :
    flatRpowExp a c x = exp (-c * x ^ (-a)) := by
  simp [flatRpowExp, hx.not_ge]

/-- Exponential decay at zero dominates every real power. -/
theorem tendsto_rpow_mul_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (s : ℝ) :
    Tendsto (fun x : ℝ ↦ x ^ s * flatRpowExp a c x) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ ↦ x ^ (-a)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos ha)
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-s / a) c hc).comp ht).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  change (x ^ (-a)) ^ (-s / a) * exp (-c * x ^ (-a)) =
    x ^ s * flatRpowExp a c x
  rw [of_pos a c hx, ← Real.rpow_mul hx.le]
  congr 2
  field_simp [ha.ne']

/-- A single generalized Laurent monomial times `flatRpowExp`. -/
private def term (a c ν d x : ℝ) : ℝ := d * x ^ ν * flatRpowExp a c x

private theorem term_tendsto_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (ν d : ℝ) :
    Tendsto (term a c ν d) (𝓝 0) (𝓝 0) := by
  have hinner : Tendsto (fun x : ℝ ↦ x ^ ν * flatRpowExp a c x) (𝓝 0) (𝓝 0) := by
    simp only [flatRpowExp, mul_ite, mul_zero]
    refine tendsto_const_nhds.if ?_
    simp only [not_le]
    refine (tendsto_rpow_mul_zero ha hc ν).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [of_pos a c hx]
  change Tendsto (fun x : ℝ ↦ d * x ^ ν * flatRpowExp a c x) (𝓝 0) (𝓝 0)
  simpa only [mul_assoc, mul_zero] using
    (tendsto_const_nhds.mul hinner :
      Tendsto (fun x : ℝ ↦ d * (x ^ ν * flatRpowExp a c x)) (𝓝 0) (𝓝 (d * 0)))

private theorem term_hasDerivAt {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (ν d x : ℝ) :
    HasDerivAt (term a c ν d)
      (term a c (ν - 1) (d * ν) x + term a c (ν - a - 1) (d * c * a) x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : term a c ν d =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [gt_mem_nhds hx] with y hy
      simp [term, zero_of_nonpos a c hy.le]
    simpa [term, zero_of_nonpos a c hx.le] using
      (hasDerivAt_const x 0).congr_of_eventuallyEq heq
  · simp only [term, zero a c, mul_zero, add_zero]
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((term_tendsto_zero ha hc (ν - 1) d).mono_left inf_le_left).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
    by_cases hypos : 0 < y
    · simp [slope_def_field, term, zero a c, of_pos a c hypos, div_eq_mul_inv]
      rw [Real.rpow_sub_one hypos.ne']
      ring
    · have hynonpos : y ≤ 0 := le_of_not_gt hypos
      simp [slope_def_field, term, zero a c, zero_of_nonpos a c hynonpos]
  · have hpow : HasDerivAt (fun y : ℝ ↦ y ^ ν) (ν * x ^ (ν - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx.ne')
    have hpow' : HasDerivAt (fun y : ℝ ↦ y ^ (-a))
        ((-a) * x ^ (-a - 1)) x := Real.hasDerivAt_rpow_const (Or.inl hx.ne')
    have hinner : HasDerivAt (fun y : ℝ ↦ -c * y ^ (-a))
        (c * a * x ^ (-a - 1)) x := by
      convert (hasDerivAt_const x (-c)).mul hpow' using 1
      all_goals ring
    have hexp : HasDerivAt (fun y : ℝ ↦ exp (-c * y ^ (-a)))
        (exp (-c * x ^ (-a)) * (c * a * x ^ (-a - 1))) x := hinner.exp
    have heq : term a c ν d =ᶠ[𝓝 x]
        ((fun _ : ℝ ↦ d) * (fun y ↦ y ^ ν)) * fun y ↦ exp (-c * y ^ (-a)) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      simp [term, of_pos a c hy]
    have hderiv := (((hasDerivAt_const x d).mul hpow).mul hexp).congr_of_eventuallyEq heq
    have hrpow : x ^ (ν - a - 1) = x ^ ν * x ^ (-a - 1) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    convert hderiv using 1
    simp [term, of_pos a c hx]
    rw [hrpow]
    ring

/-- A finite sum of generalized Laurent monomials times `flatRpowExp`. -/
private def sum (a c : ℝ) (p : Multiset (ℝ × ℝ)) (x : ℝ) : ℝ :=
  (p.map fun q ↦ term a c q.1 q.2 x).sum

private theorem sum_hasDerivAt {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (p : Multiset (ℝ × ℝ)) : ∃ q : Multiset (ℝ × ℝ),
      ∀ x, HasDerivAt (sum a c p) (sum a c q x) x := by
  induction p using Multiset.induction_on with
  | empty =>
      exact ⟨0, fun x ↦ by simpa [sum] using hasDerivAt_const x 0⟩
  | @cons head tail ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨(head.1 - 1, head.2 * head.1) ::ₘ
        (head.1 - a - 1, head.2 * c * a) ::ₘ q, fun x ↦ ?_⟩
      have h := (term_hasDerivAt ha hc head.1 head.2 x).add (hq x)
      convert h using 1
      · ext y
        simp [sum]
      · simp [sum, add_assoc]

private theorem sum_contDiff {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (p : Multiset (ℝ × ℝ)) {n : ℕ∞} : ContDiff ℝ n (sum a c p) := by
  apply contDiff_all_iff_nat.2 (fun m ↦ ?_) n
  induction m generalizing p with
  | zero =>
      exact contDiff_zero.2 <| continuous_iff_continuousAt.2 fun x ↦
        ((sum_hasDerivAt ha hc p).choose_spec x).continuousAt
  | succ m ih =>
      obtain ⟨q, hq⟩ := sum_hasDerivAt ha hc p
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
      refine contDiff_succ_iff_deriv.2 ⟨fun x ↦ (hq x).differentiableAt, by simp, ?_⟩
      convert ih q using 2
      funext x
      exact (hq x).deriv

private theorem sum_iteratedDeriv_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (p : Multiset (ℝ × ℝ)) (n : ℕ) : iteratedDeriv n (sum a c p) 0 = 0 := by
  induction n generalizing p with
  | zero => simp [sum, term]
  | succ n ih =>
      obtain ⟨q, hq⟩ := sum_hasDerivAt ha hc p
      rw [iteratedDeriv_succ']
      have hderiv : deriv (sum a c p) = sum a c q := funext fun x ↦ (hq x).deriv
      rw [hderiv]
      exact ih q

/-- Multiplying `flatRpowExp a c` by an arbitrary real power preserves smoothness. -/
@[fun_prop]
theorem rpow_mul_contDiff {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (s : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (fun x ↦ x ^ s * flatRpowExp a c x) := by
  convert sum_contDiff (n := n) ha hc ({(s, 1)} : Multiset (ℝ × ℝ)) using 1
  funext x
  simp [sum, term]

/-- Every iterated derivative of `x ^ s * flatRpowExp a c x` vanishes at the origin. -/
theorem rpow_mul_iteratedFDeriv_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (s : ℝ)
    (n : ℕ) : iteratedFDeriv ℝ n (fun x ↦ x ^ s * flatRpowExp a c x) 0 = 0 := by
  have hfun : (fun x ↦ x ^ s * flatRpowExp a c x) =
      sum a c ({(s, 1)} : Multiset (ℝ × ℝ)) := by
    funext x
    simp [sum, term]
  rw [hfun, ← norm_eq_zero, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    sum_iteratedDeriv_zero ha hc]
  simp

/-- Every iterated derivative of `flatRpowExp a c` vanishes at the origin. -/
theorem iteratedFDeriv_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (n : ℕ) :
    iteratedFDeriv ℝ n (flatRpowExp a c) 0 = 0 := by
  simpa using rpow_mul_iteratedFDeriv_zero ha hc 0 n

/-- `flatRpowExp a c` is smooth when both parameters are positive. -/
@[fun_prop]
theorem contDiff {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {n : ℕ∞} :
    ContDiff ℝ n (flatRpowExp a c) := by
  convert sum_contDiff (n := n) ha hc ({(0, 1)} : Multiset (ℝ × ℝ)) using 1
  funext x
  simp [sum, term]

end flatRpowExp

end Real
