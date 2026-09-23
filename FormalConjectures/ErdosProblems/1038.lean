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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1038

*Reference:*
 - [erdosproblems.com/1038](https://www.erdosproblems.com/1038)
 - [Tao25] Tao, Terence. Sublevel Sets of Logarithmic Potentials. Terry Tao’s Blog, Dec. 2025
  (https://terrytao.wordpress.com/wp-content/uploads/2025/12/erdos-1038-1.pdf)
 - [EHP58] Erdős, P., Herzog, F., Piranian, G. Metric properties of polynomials.
  J. Analyse Math. 6 (1958), 125--148.

### AI disclosure

Lean 4 code in this file was drafted with assistance from OpenAI Codex and Claude (Anthropic).
The mathematical content and references are the author's own work.
-/

@[expose] public section

open scoped Real ENNReal
open MeasureTheory Set

namespace Erdos1038

/-- What is the infimum of `|{x ∈ ℝ : |f x| < 1}|` over all nonconstant monic polynomials `f` such
that all of its roots are real and contained in `[-1,1]`? -/
@[category research open, AMS 28]
theorem erdos_1038.parts.i : answer(sorry) =
    ⨅ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1} := by
  sorry

/-- The supremum of `|{x ∈ ℝ : |f x| < 1}|` over all monic polynomials `f` such that
all of its roots are real and contained in `[-1,1]` is `2 * 2 ^ (1 / 2)`. This is proved in
[Tao25]. -/
@[category research solved, AMS 28]
theorem erdos_1038.parts.ii : 2 * 2 ^ (1 / 2 : ℝ) =
    ⨆ f : {f : Polynomial ℝ // f.Monic ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1} := by
  sorry

/-- The infimum of `|{x ∈ ℝ : |f x| < 1}|` over all nonconstant monic polynomials `f` such that
all of its roots are real and contained in `[-1,1]` is `< 1.835`. -/
@[category research solved, AMS 28]
theorem erdos_1038.variants.inf_upperBound : ⨅ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1} < 1.835 := by
  sorry

/-- The infimum of `|{x ∈ ℝ : |f x| < 1}|` over all nonconstant monic polynomials `f` such that
all of its roots are real and contained in `[-1,1]` is `≥ 2 ^ (4 / 3) - 1`. -/
@[category research solved, AMS 28]
theorem erdos_1038.variants.inf_lowerBound : 2 ^ (4 / 3 : ℝ) - 1 ≤
    ⨅ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1} := by
  sorry


/-- For a monic quadratic with roots at distance at most two, the sublevel measure
is $2\sqrt{1+d^2}$, where $2|d|$ is the distance between the roots. This gives
the degree-two case of the sublevel-set problem in [Tao25]. -/
@[category textbook, AMS 28]
theorem erdos_1038.variants.quadratic_sublevel_formula (m d : ℝ) (hd : |d| ≤ 1) :
    volume {x : ℝ | |(x - m) ^ 2 - d ^ 2| < 1} =
      ENNReal.ofReal (2 * Real.sqrt (1 + d ^ 2)) := by
  have hd2 : d ^ 2 ≤ 1 := by nlinarith [abs_le.mp hd |>.1, abs_le.mp hd |>.2]
  have hs : 0 < Real.sqrt (1 + d ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (1 + d ^ 2) ^ 2 = 1 + d ^ 2 := Real.sq_sqrt (by positivity)
  let I := Ioo (m - Real.sqrt (1 + d ^ 2)) (m + Real.sqrt (1 + d ^ 2))
  have hupper : {x : ℝ | |(x - m) ^ 2 - d ^ 2| < 1} ⊆ I := by
    intro x hx
    change |(x-m)^2-d^2| < 1 at hx
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hx
    constructor
    · nlinarith [sq_nonneg (x - m + Real.sqrt (1 + d ^ 2))]
    · nlinarith [sq_nonneg (x - m - Real.sqrt (1 + d ^ 2))]
  have hlower : I \ {m} ⊆ {x : ℝ | |(x - m) ^ 2 - d ^ 2| < 1} := by
    rintro x ⟨⟨hlo, hhi⟩, hne⟩
    have hpos : 0 < (x - m) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    have hlt : (x - m) ^ 2 < 1 + d ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hhi) (sub_pos.mpr hlo)]
    change |(x-m)^2-d^2| < 1
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hI : volume I = ENNReal.ofReal (2 * Real.sqrt (1 + d ^ 2)) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  apply le_antisymm
  · calc
      _ ≤ volume I := measure_mono hupper
      _ = _ := hI
  · have h : volume (I \ {m}) ≤ volume {x : ℝ | |(x-m)^2-d^2| < 1} :=
      measure_mono hlower
    rwa [measure_sdiff_null (by simp), hI] at h

/-- The degree-two case of the supremum bound in [Tao25]: if $a,b\in[-1,1]$,
the sublevel set of $(x-a)(x-b)$ has measure at most $2\sqrt{2}$. -/
@[category textbook, AMS 28]
theorem erdos_1038.variants.quadratic_upperBound (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    volume {x : ℝ | |(x-a)*(x-b)| < 1} ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  have hd : |(a-b)/2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [abs_le.mp ha |>.1, abs_le.mp ha |>.2,
      abs_le.mp hb |>.1, abs_le.mp hb |>.2]
  have hpoly (x : ℝ) : (x-a)*(x-b) = (x-(a+b)/2)^2 - ((a-b)/2)^2 := by ring
  simp_rw [hpoly]
  rw [erdos_1038.variants.quadratic_sublevel_formula ((a+b)/2) ((a-b)/2) hd]
  apply ENNReal.ofReal_le_ofReal
  have hd2 : ((a-b)/2)^2 ≤ 1 := by nlinarith [abs_le.mp hd |>.1, abs_le.mp hd |>.2]
  have h := Real.sqrt_le_sqrt (show 1 + ((a-b)/2)^2 ≤ 2 by linarith)
  linarith


/-- The admissible quadratic $x^2-1$, with roots $-1$ and $1$, attains the supremum
value $2\sqrt{2}$ in [Tao25]. -/
@[category textbook, AMS 28]
theorem erdos_1038.variants.quadratic_extremizer :
    volume {x : ℝ | |x ^ 2 - 1| < 1} = ENNReal.ofReal (2 * Real.sqrt 2) := by
  convert erdos_1038.variants.quadratic_sublevel_formula 0 1 (by norm_num) using 1 <;>
    norm_num

open Polynomial in
/-- The lower half of `erdos_1038.parts.ii`: the supremum is at least $2\sqrt{2}$, because the
admissible polynomial $x^2-1$ has sublevel measure exactly $2\sqrt{2}$. The matching upper bound
is proved in [Tao25]. -/
@[category textbook, AMS 28]
theorem erdos_1038.variants.sup_lowerBound : 2 * 2 ^ (1 / 2 : ℝ) ≤
    ⨆ f : {f : Polynomial ℝ // f.Monic ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1} := by
  have hroots : (X ^ 2 - C 1 : ℝ[X]).roots = {-1, 1} := nthRoots_two_one
  refine le_iSup_of_le ⟨X ^ 2 - C 1, monic_X_pow_sub_C 1 two_ne_zero, ?_⟩ ?_
  · rw [hroots, natDegree_X_pow_sub_C]
    norm_num [Multiset.filter_singleton]
  · simp only [eval_sub, eval_pow, eval_X, eval_C]
    rw [erdos_1038.variants.quadratic_extremizer, ENNReal.ofReal_mul zero_le_two,
      Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg zero_le_two (by norm_num)]
    norm_num

open Polynomial in
/-- The infimum in `erdos_1038.parts.i` is at most $2$: the polynomial $f(x)=x$ is admissible
and its sublevel set $\{x : |x| < 1\} = (-1,1)$ has measure $2$. -/
@[category textbook, AMS 28]
theorem erdos_1038.variants.inf_le_two : ⨅ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1} ≤ 2 := by
  refine iInf_le_of_le ⟨X, monic_X, by simpa using X_ne_C (1 : ℝ), ?_⟩ ?_
  · rw [roots_X, natDegree_X]
    norm_num [Multiset.filter_singleton]
  · have h : {x : ℝ | |eval x X| < 1} = Ioo (-1) 1 := by
      ext x
      simp [abs_lt]
    rw [h, Real.volume_Ioo]
    norm_num

open Polynomial in
/-- The infimum in `erdos_1038.parts.i` is strictly less than $2$, as observed in [EHP58]:
for $f(x)=(x+1)(x-1)^3$ the sublevel set $\{x : |f(x)| < 1\}$ is contained in
$(-1.108,-0.835)\cup(0,1.718)$, whose total length is $1.991$. -/
@[category textbook, AMS 28]
theorem erdos_1038.variants.inf_lt_two : ⨅ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
    volume {x | |f.1.eval x| < 1} < 2 := by
  have hmonic : ((X + C 1) * (X - C 1) ^ 3 : ℝ[X]).Monic :=
    (monic_X_add_C 1).mul ((monic_X_sub_C 1).pow 3)
  have hdeg : ((X + C 1) * (X - C 1) ^ 3 : ℝ[X]).natDegree = 4 := by
    rw [(monic_X_add_C 1).natDegree_mul ((monic_X_sub_C 1).pow 3),
      (monic_X_sub_C 1).natDegree_pow, natDegree_X_add_C, natDegree_X_sub_C]
  have hne : ((X + C 1) * (X - C 1) ^ 3 : ℝ[X]) ≠ 1 := fun h => by
    rw [h, natDegree_one] at hdeg
    exact absurd hdeg (by norm_num)
  have hcard : (((X + C 1) * (X - C 1) ^ 3 : ℝ[X]).roots.filter
      fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = ((X + C 1) * (X - C 1) ^ 3 : ℝ[X]).natDegree := by
    rw [roots_mul hmonic.ne_zero, roots_X_add_C, roots_pow, roots_X_sub_C, hdeg]
    norm_num [Multiset.filter_singleton, Multiset.filter_nsmul]
  refine lt_of_le_of_lt (iInf_le _ ⟨(X + C 1) * (X - C 1) ^ 3, hmonic, hne, hcard⟩) ?_
  simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_X, eval_C]
  have hsub : {x : ℝ | |(x + 1) * (x - 1) ^ 3| < 1} ⊆
      Ioo (-277 / 250) (-167 / 200) ∪ Ioo 0 (859 / 500) := by
    intro x (hx : |(x + 1) * (x - 1) ^ 3| < 1)
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hx
    rcases le_or_gt x (-277 / 250) with h1 | h1
    · have ht : 0 ≤ -277 / 250 - x := by linarith
      nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]
    rcases lt_or_ge x (-167 / 200) with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    rcases le_or_gt x 0 with h3 | h3
    · have hs : 0 ≤ x + 167 / 200 := by linarith
      have hp : 0 ≤ x ^ 3 - 2 * x ^ 2 + 2 := by
        nlinarith [mul_nonneg hs (neg_nonneg.mpr h3), pow_nonneg hs 3]
      nlinarith [mul_nonneg (neg_nonneg.mpr h3) hp]
    rcases lt_or_ge x (859 / 500) with h4 | h4
    · exact Or.inr ⟨h3, h4⟩
    · have ht : 0 ≤ x - 859 / 500 := by linarith
      nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]
  calc volume {x : ℝ | |(x + 1) * (x - 1) ^ 3| < 1}
      ≤ volume (Ioo (-277 / 250 : ℝ) (-167 / 200) ∪ Ioo 0 (859 / 500)) := measure_mono hsub
    _ ≤ volume (Ioo (-277 / 250 : ℝ) (-167 / 200)) + volume (Ioo (0 : ℝ) (859 / 500)) :=
      measure_union_le _ _
    _ < 2 := by
      rw [Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ENNReal.ofReal_lt_iff_lt_toReal (by norm_num) (by norm_num)]
      norm_num

end Erdos1038
