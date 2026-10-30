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
# Ben Green's Open Problem 35

Estimate the infimum of the $L^p$ norm of the self-convolution of a nonnegative integrable
function supported on $[0,1]$ with total integral $1$.

We model a function `f : [0,1] → ℝ≥0` as a function `f : ℝ → ℝ` that is nonnegative, integrable,
supported on `[0,1]`, and has total integral `1`.

*References:*
- [Ben Green's Open Problem 35](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.35)
- [Gr01](https://people.maths.ox.ac.uk/greenbj/papers/number-of-squares-and-Bh%5Bg%5D.pdf)
  B. J. Green, *The number of squares and $B_h[g]$-sets*, Acta Arith. 100 (2001), no. 4, 365-390.
- [CS17](https://arxiv.org/abs/1403.7988)
  A. Cloninger and S. Steinerberger, *On suprema of autoconvolutions with an application to Sidon
  sets*, Proc. Amer. Math. Soc. 145 (2017), no. 8, 3191-3200.
- [MV10](https://arxiv.org/abs/0907.1379)
  M. Matolcsi and C. Vinuesa, *Improved bounds on the supremum of autoconvolutions*,
  J. Math. Anal. Appl. 372 (2010), 439-447.
- [AE25](https://arxiv.org/abs/2506.13131)
  A. Novikov et al., *AlphaEvolve: A coding agent for scientific and algorithmic discovery*,
  arXiv:2506.13131 (2025), Appendix B.1.
- [GGTW25](https://arxiv.org/abs/2511.02864)
  B. Georgiev, J. Gómez-Serrano, T. Tao and A. Z. Wagner, *Mathematical exploration and discovery
  at scale*, arXiv:2511.02864 (2025), Section 6.2.

The constants of [CS17], [MV10], [AE25] and [GGTW25] are stated for functions supported on
$[-1/4, 1/4]$; rescaling to $[0, 1]$ halves them.
-/

@[expose] public section

namespace Green35

open MeasureTheory
open scoped Convolution ENNReal

/-- A nonnegative integrable function on $[0,1]$ with total integral $1$. -/
def IsUnitIntervalDensity (f : ℝ → ℝ) : Prop :=
  Integrable f ∧ (∀ x, 0 ≤ f x) ∧ Function.support f ⊆ .Icc (0 : ℝ) 1 ∧ ∫ x, f x = 1

/-- The infimum of $\|f \ast f\|_p$ over unit-interval densities. -/
noncomputable def c (p : ℝ≥0∞) : ℝ≥0∞ :=
  sInf { r | ∃ f, IsUnitIntervalDensity f ∧ r = eLpNorm (f ⋆ f) p }

def green_35.lower.answer : ℝ≥0∞ → ℝ≥0∞ := sorry

/-- Lower bound for $c(p)$ for $1 < p \le \infty$, improving the known value $\sqrt{4/7}$ at
$p = 2$ or the known value $0.64$ at $p = \infty$. -/
@[category research open, question value, AMS 26 28 42]
theorem green_35.lower :
    (∀ p, 1 < p → green_35.lower.answer p ≤ c p) ∧
      (ENNReal.ofReal (Real.sqrt (4 / 7)) < green_35.lower.answer 2 ∨
        0.64 < green_35.lower.answer ∞) := by
  sorry

def green_35.upper.answer : ℝ≥0∞ → ℝ≥0∞ := sorry

/-- Upper bound for $c(p)$ for $1 < p \le \infty$, improving the best-known value $0.7516$ at
$p = \infty$. -/
@[category research open, question value, AMS 26 28 42]
theorem green_35.upper :
    (∀ p, 1 < p → c p ≤ green_35.upper.answer p) ∧ green_35.upper.answer ∞ < 0.7516 := by
  sorry

/-! ## The Matolcsi–Vinuesa step function

The bound `variants.c_inf_upper` uses the step function of [MV10] and the general bound
`StepFunction.step_conv_le`. -/

open StepFunction

/-- A step function with nonnegative heights summing to `n` is a unit-interval density. -/
@[category API, AMS 26 28]
lemma step_isUnitIntervalDensity (n : ℕ) (hn : 0 < n) (c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hsum : ∑ i ∈ Finset.range n, c i = n) : IsUnitIntervalDensity (step n c) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨integrable_step n c, step_nonneg n hc, support_step_subset n c, ?_⟩
  rw [integral_step n hn, hsum, div_self hn'.ne']

namespace MV10

/-- The 208 step heights of [MV10, appendix], scaled by `10⁸`. -/
def heights : List ℕ := [
  121174638, 0, 0, 25997048, 47606812, 62295219, 32965860, 0,
  29734381, 0, 0, 0, 0, 0, 0, 0,
  846453, 5731673, 0, 13014906, 0, 8357863, 5268549, 6456956,
  6158231, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 2396999, 0, 0,
  5846552, 0, 0, 0, 0, 0, 263320, 5098350,
  0, 12833130, 9049240, 21232176, 24866151, 9933512, 1963586, 1363895,
  32389841, 0, 0, 14467517, 1297520, 0, 0, 16299837,
  38329665, 11361262, 32074656, 17344291, 33181372, 24357561, 25770030, 20567824,
  13085743, 17116496, 14349025, 7019695, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 1317410, 3425410, 4275650,
  3045044, 7900079, 7020678, 8528342, 9705597, 9328960, 9360206, 6227754,
  7943462, 8176106, 10667185, 10178412, 11421821, 7773213, 11021377, 12190377,
  6572457, 7494855, 0, 0, 2140202, 0, 0, 2314780,
  127997, 0, 4672881, 3886266, 11141784, 695668, 4662240, 3543131,
  8803511, 4165729, 10785652, 6747342, 18785215, 31908323, 32497050, 9824861,
  23309878, 12428441, 3200975, 9331630, 9527521, 12202693, 13179059, 9266878,
  2013746, 16448047, 20324945, 21810431, 27321179, 25242816, 19993811, 13683837,
  13304836, 8794214, 12893672, 16904485, 22510883, 26079786, 27367504, 26271896,
  20457964, 15073917, 11014028, 9896000, 9260690, 13269111, 17329988, 20761774,
  21707182, 18933169, 14601258, 8531506, 6187865, 6100211, 9064962, 12781018,
  17038096, 18576600, 17345010, 14667009, 9569536, 6092822, 3219067, 4955870,
  9657756, 16382398, 22606693, 22230709, 19833621, 16155032, 9330751, 2838363,
  2769322, 3349924, 9448887, 20517242, 22849741, 24175836, 19700135, 18168723]

/-- The `i`-th height, `0` past the end. -/
def A (i : ℕ) : ℕ := heights.getD i 0

@[category API, AMS 26]
lemma A_eq_zero {i : ℕ} (hi : 208 ≤ i) : A i = 0 := by
  have : heights.length = 208 := rfl
  rw [A, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-- `∑ A i`. -/
def S : ℕ := 2039607811

@[category API, AMS 26]
lemma sum_A : ∑ i ∈ Finset.range 208, A i = S := by decide +kernel

/-- The exact-arithmetic check: `208 · max_k (A ⋆ A)_k ≤ 0.7549 · S²`. -/
@[category API, AMS 26]
lemma check : ∀ k < 2 * 208,
    10000 * 208 * ∑ i ∈ Finset.range (k + 1), A i * A (k - i) ≤ 7549 * S ^ 2 := by
  decide +kernel

/-- The heights normalised so that `∫ f = 1` on `[0, 1]`. -/
noncomputable def w (i : ℕ) : ℝ := 208 * A i / S

@[category API, AMS 26 28]
lemma conv_le (x : ℝ) : (step 208 w ⋆ step 208 w) x ≤ 7549 / 10000 := by
  have hS : (0 : ℝ) < S := by norm_num [S]
  have h := step_conv_le 208 (by norm_num) w (7549 / 10000 * 208)
    (fun i ↦ by unfold w; positivity) (fun k hk ↦ ?_) x
  · simpa using h
  have hw : ∀ i, w i = 208 / S * A i := fun i ↦ by unfold w; ring
  have hsum : (∑ i ∈ Finset.range 208, ∑ j ∈ Finset.range 208,
      (if i + j = k then w i * w j else 0)) = (208 / S) * (208 / S) *
      ∑ i ∈ Finset.range 208, ∑ j ∈ Finset.range 208,
        (if i + j = k then (A i : ℝ) * A j else 0) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp [hw]; ring
  rw [hsum]
  have := sum_ite_add_eq 208 k (fun i ↦ (A i : ℝ)) (fun i hi ↦ by simp [A_eq_zero hi])
  rw [this]
  have hc := check k hk
  have hc' : (10000 * 208 : ℝ) * ∑ i ∈ Finset.range (k + 1), (A i : ℝ) * A (k - i) ≤
      7549 * (S : ℝ) ^ 2 := by exact_mod_cast hc
  rw [div_mul_div_comm, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

end MV10

/-  Known bounds and comparisons. -/
namespace variants

/-- Lower bound for $c(2)$ from Green's first paper ([Gr01]); the constant is `sqrt(4/7)` (about 0.7559). -/
@[category research solved, AMS 26 28 42]
theorem c_2_lower : ENNReal.ofReal (Real.sqrt (4 / 7)) ≤ c 2 := by
  sorry

/-- Best-known lower bound for $c(\infty)$ due to Cloninger and Steinerberger ([CS17]). -/
@[category research solved, AMS 26 28 42]
theorem c_inf_lower : 0.64 ≤ c ∞ := by
  sorry

open MV10 in
/-- Upper bound for $c(\infty)$ due to Matolcsi and Vinuesa ([MV10]); their step function has
autoconvolution supremum $1.50972\ldots$, which rescales to $0.75486\ldots$. -/
@[category research solved, AMS 26 28 42, formal_proof using formal_conjectures at
  "https://github.com/casens5/formal-conjectures/commit/485732602d00faef71bdd42220b79b4791420678"]
theorem c_inf_upper : c ∞ ≤ 0.7549 := by
  have hS : (0 : ℝ) < S := by norm_num [S]
  have hw : ∀ i, 0 ≤ w i := fun i ↦ by unfold w; positivity
  have hf : IsUnitIntervalDensity (step 208 w) := by
    refine step_isUnitIntervalDensity 208 (by norm_num) w hw ?_
    have : (∑ i ∈ Finset.range 208, (A i : ℝ)) = S := by exact_mod_cast sum_A
    simp only [w, ← Finset.sum_div, ← Finset.mul_sum, this]
    field_simp
    norm_num
  have hc : c ∞ ≤ eLpNorm (step 208 w ⋆ step 208 w) ∞ := by
    unfold c
    exact sInf_le ⟨_, hf, rfl⟩
  refine hc.trans ?_
  rw [eLpNorm_exponent_top]
  refine (eLpNormEssSup_le_of_ae_bound (C := 7549 / 10000)
    (Filter.Eventually.of_forall fun x ↦ ?_)).trans_eq ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (step_conv_nonneg _ hw x)]
    exact conv_le x
  · have h : (0.7549 : ℝ≥0∞) = ((0.7549 : NNReal) : ℝ≥0∞) := rfl
    rw [h, ENNReal.ofReal]
    congr 1
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num), NNReal.coe_ofScientific]
    norm_num

/-- Upper bound for $c(\infty)$ found by AlphaEvolve ([AE25]) and recorded in Green's 2025
update; the step function there has autoconvolution supremum at most $1.5053$, which rescales to
$0.75265$. -/
@[category research solved, AMS 26 28 42]
theorem c_inf_upper_ae25 : c ∞ ≤ 0.75265 := by
  sorry

/-- Best-known upper bound for $c(\infty)$ ([GGTW25], §6.2): a step function with autoconvolution
supremum at most $1.5032$, which rescales to $0.7516$. -/
@[category research solved, AMS 26 28 42]
theorem c_inf_upper_ggtw25 : c ∞ ≤ 0.7516 := by
  sorry

/-- A comparison bound from Young's inequality. -/
@[category textbook, AMS 26 28 42]
theorem c_inf_lower_young : (c 2) ^ 2 ≤ c ∞ := by
  sorry

end variants

end Green35
