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

/-!
# Erdős Problem 655

*Reference:* [erdosproblems.com/655](https://www.erdosproblems.com/655)
-/

open Filter Finset EuclideanGeometry
open scoped Real

namespace Erdos655

/-- A collection $x_1, \dots, x_n\in\mathbb{R}^2$ is _valid_ if
no circle whose centre is one of the $x_i$ contains three other points. -/
def IsValid (X : Finset ℝ²) : Prop :=
  ∀ᵉ (x ∈ X) (r > 0), ¬3 ≤ (Metric.sphere x r ∩ X).ncard

/-
## The regular `n`-gon

The literal conjecture below is *false*: Zach Hunter observed that `n` points equally spaced on a
circle form a valid configuration with only `⌊n/2⌋` distinct distances, far fewer than `(1+c)n/2`.
We formalise this construction and the resulting disproof. The vertices of the regular `n`-gon are
`V n k = (cos (2πk/n), sin (2πk/n))`.
-/

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle. -/
noncomputable def V (n k : ℕ) : ℝ² := !₂[Real.cos (2 * π * k / n), Real.sin (2 * π * k / n)]

section NgonHelpers

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

/-- Squared distance between two vertices, via the cosine-difference identity. -/
private lemma V_dist_sq (n i j : ℕ) :
    dist (V n i) (V n j) ^ 2 = 2 - 2 * Real.cos (2 * π * i / n - 2 * π * j / n) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [V, Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq]
  have hc := Real.cos_sub (2 * π * i / n) (2 * π * j / n)
  have e1 := Real.sin_sq_add_cos_sq (2 * π * i / n)
  have e2 := Real.sin_sq_add_cos_sq (2 * π * j / n)
  rw [sq_abs, sq_abs]
  nlinarith [hc, e1, e2]

/-- Every vertex lies on the unit circle centred at the origin. -/
private lemma V_on_circle (n k : ℕ) : dist (V n k) (!₂[(0:ℝ), 0]) = 1 := by
  have h2 : dist (V n k) (!₂[(0:ℝ), 0]) ^ 2 = 1 := by
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
    simp only [V, Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq]
    have e1 := Real.sin_sq_add_cos_sq (2 * π * k / n)
    rw [sq_abs, sq_abs]; nlinarith [e1]
  nlinarith [dist_nonneg (x := V n k) (y := (!₂[(0:ℝ), 0])), h2]

/-- The cosine of the angle between vertices `i` and `j` equals that of a "folded"
index `d ∈ [1, n/2]`. -/
private lemma V_cos_fold (n i j : ℕ) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ∃ d, 1 ≤ d ∧ d ≤ n / 2 ∧
      Real.cos (2 * π * i / n - 2 * π * j / n) = Real.cos (2 * π * d / n) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hi
  obtain ⟨a, ha1, han, hcos_a⟩ :
      ∃ a, 1 ≤ a ∧ a ≤ n - 1 ∧
        Real.cos (2 * π * i / n - 2 * π * j / n) = Real.cos (2 * π * a / n) := by
    rcases le_total i j with h | h
    · refine ⟨j - i, by omega, by omega, ?_⟩
      have : 2 * π * i / n - 2 * π * j / n = -(2 * π * (j - i : ℕ) / n) := by
        push_cast [Nat.cast_sub h]; ring
      rw [this, Real.cos_neg]
    · refine ⟨i - j, by omega, by omega, ?_⟩
      have : 2 * π * i / n - 2 * π * j / n = 2 * π * (i - j : ℕ) / n := by
        push_cast [Nat.cast_sub h]; ring
      rw [this]
  refine ⟨min a (n - a), by omega, by omega, ?_⟩
  rw [hcos_a]
  rcases le_total a (n - a) with hle | hle
  · rw [min_eq_left hle]
  · rw [min_eq_right hle]
    have hnpos : ((n : ℝ)) ≠ 0 := by positivity
    have hna : (2 * π * a / n) = 2 * π - 2 * π * (n - a : ℕ) / n := by
      push_cast [Nat.cast_sub (by omega : a ≤ n)]
      field_simp
      ring
    rw [hna, show (2 * π - 2 * π * (n - a : ℕ) / n)
        = -(2 * π * (n - a : ℕ) / n) + 2 * π by ring, Real.cos_add_two_pi, Real.cos_neg]

/-- Each pairwise distance equals a "canonical" distance `dist (V 0) (V d)` with `d ∈ [1, n/2]`. -/
private lemma V_dist_eq_fold (n i j : ℕ) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ∃ d, 1 ≤ d ∧ d ≤ n / 2 ∧ dist (V n i) (V n j) = dist (V n 0) (V n d) := by
  obtain ⟨d, hd1, hd2, hcos⟩ := V_cos_fold n i j hi hj hij
  refine ⟨d, hd1, hd2, ?_⟩
  have h1 := V_dist_sq n i j
  have h2 := V_dist_sq n 0 d
  have hcos0 : Real.cos (2 * π * ((0:ℕ):ℝ) / n - 2 * π * d / n) = Real.cos (2 * π * d / n) := by
    simp only [Nat.cast_zero, mul_zero, zero_div, zero_sub, Real.cos_neg]
  have hsq : dist (V n i) (V n j) ^ 2 = dist (V n 0) (V n d) ^ 2 := by
    rw [h1, h2, hcos, hcos0]
  nlinarith [dist_nonneg (x := V n i) (y := V n j),
    dist_nonneg (x := V n 0) (y := V n d), hsq]

/-- The vertex map is injective on `{0, …, n-1}`. -/
private lemma V_injOn (n : ℕ) : Set.InjOn (V n) (↑(Finset.range n)) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hn : 0 < n := by omega
  have hnr : ((n : ℝ)) ≠ 0 := by positivity
  have hi' : (i : ℝ) < n := by exact_mod_cast hi
  have hj' : (j : ℝ) < n := by exact_mod_cast hj
  have hc : Real.cos (2 * π * i / n) = Real.cos (2 * π * j / n) := by
    have h0 : (V n i) 0 = (V n j) 0 := by rw [hij]
    simpa [V] using h0
  have hs : Real.sin (2 * π * i / n) = Real.sin (2 * π * j / n) := by
    have h1 : (V n i) 1 = (V n j) 1 := by rw [hij]
    simpa [V] using h1
  have hcos1 : Real.cos (2 * π * i / n - 2 * π * j / n) = 1 := by
    rw [Real.cos_sub, hc, hs]
    nlinarith [Real.sin_sq_add_cos_sq (2 * π * (j : ℝ) / n)]
  rw [Real.cos_eq_one_iff] at hcos1
  obtain ⟨m, hm⟩ := hcos1
  field_simp at hm
  have hmlt : |(m : ℝ)| < 1 := by
    have hij' : |(i : ℝ) - j| < n := by rw [abs_lt]; constructor <;> linarith
    have heq : |(m : ℝ)| * n = |(i : ℝ) - j| := by
      rw [← hm, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ n)]
    nlinarith [heq, hij', abs_nonneg (m : ℝ), (by positivity : (0:ℝ) < n)]
  have hm0 : m = 0 := by
    rcases abs_lt.mp hmlt with ⟨h1, h2⟩
    have hb1 : (-1 : ℤ) < m := by exact_mod_cast h1
    have hb2 : m < (1 : ℤ) := by exact_mod_cast h2
    omega
  subst hm0
  simp only [Int.cast_zero, zero_mul] at hm
  have : (i : ℝ) = j := by linarith
  exact_mod_cast this

/-- The regular `n`-gon as a `Finset ℝ²`. -/
noncomputable def ngon (n : ℕ) : Finset ℝ² := (Finset.range n).image (V n)

@[simp] lemma ngon_card (n : ℕ) : (ngon n).card = n := by
  rw [ngon, Finset.card_image_of_injOn (V_injOn n), Finset.card_range]

private lemma ngon_on_circle (n : ℕ) {p : ℝ²} (hp : p ∈ ngon n) :
    dist p (!₂[(0:ℝ), 0]) = 1 := by
  rw [ngon, Finset.mem_image] at hp
  obtain ⟨k, _, rfl⟩ := hp
  exact V_on_circle n k

/-- The regular `n`-gon determines at most `n/2` distinct distances. -/
lemma distinctDistances_ngon_le (n : ℕ) : distinctDistances (ngon n) ≤ n / 2 := by
  unfold distinctDistances
  have hsub : (ngon n).offDiag.image (fun p : ℝ² × ℝ² => dist p.1 p.2) ⊆
      (Finset.Icc 1 (n / 2)).image (fun d => dist (V n 0) (V n d)) := by
    intro w hw
    simp only [Finset.mem_image, Finset.mem_offDiag] at hw
    obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩ := hw
    rw [ngon, Finset.mem_image] at ha hb
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := hb
    simp only [Finset.mem_range] at hi hj
    have hijne : i ≠ j := fun h => hab (by rw [h])
    obtain ⟨d, hd1, hd2, hdist⟩ := V_dist_eq_fold n i j hi hj hijne
    exact Finset.mem_image.mpr ⟨d, Finset.mem_Icc.mpr ⟨hd1, hd2⟩, hdist.symm⟩
  calc (((ngon n).offDiag.image (fun p : ℝ² × ℝ² => dist p.1 p.2)).card)
      ≤ ((Finset.Icc 1 (n / 2)).image (fun d => dist (V n 0) (V n d))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 (n / 2)).card := Finset.card_image_le
    _ = n / 2 := by rw [Nat.card_Icc]; omega

/-- The regular `n`-gon is valid: no circle centred at a vertex contains three vertices, because all
vertices lie on a common circle, which meets any vertex-centred circle in at most two points. -/
lemma isValid_ngon (n : ℕ) : IsValid (ngon n) := by
  rintro x hx r hr hge
  have hset : Metric.sphere x r ∩ (↑(ngon n) : Set ℝ²)
      = ↑((ngon n).filter (fun p => dist p x = r)) := by
    ext p
    simp only [Set.mem_inter_iff, Metric.mem_sphere, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_coe]
    tauto
  rw [hset, Set.ncard_coe_finset] at hge
  have hge2 : 2 < ((ngon n).filter (fun p => dist p x = r)).card := by omega
  obtain ⟨p₁, p₂, p₃, h1, h2, h3, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp hge2
  simp only [Finset.mem_filter] at h1 h2 h3
  have hx1 : dist x (!₂[(0:ℝ), 0]) = 1 := ngon_on_circle n hx
  have hxne : x ≠ (!₂[(0:ℝ), 0]) := by
    intro h; rw [h, dist_self] at hx1; norm_num at hx1
  set s₁ : EuclideanGeometry.Sphere ℝ² := ⟨x, r⟩ with hs1
  set s₂ : EuclideanGeometry.Sphere ℝ² := ⟨!₂[(0:ℝ), 0], 1⟩ with hs2
  have hsne : s₁ ≠ s₂ := fun h => hxne (congrArg EuclideanGeometry.Sphere.center h)
  have hm₁ : ∀ p, dist p x = r → p ∈ s₁ := fun p hp => by
    rw [EuclideanGeometry.mem_sphere]; exact hp
  have hm₂ : ∀ p, p ∈ ngon n → p ∈ s₂ := fun p hp => by
    rw [EuclideanGeometry.mem_sphere]; exact ngon_on_circle n hp
  have hconcl := EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
    (finrank_euclideanSpace_fin) hsne h12
    (hm₁ p₁ h1.2) (hm₁ p₂ h2.2) (hm₁ p₃ h3.2)
    (hm₂ p₁ h1.1) (hm₂ p₂ h2.1) (hm₂ p₃ h3.1)
  rcases hconcl with h | h
  · exact h13 h.symm
  · exact h23 h.symm

end NgonHelpers

/--
Let $x_1,\ldots,x_n\in \mathbb{R}^2$ be such that no circle whose centre is one
of the $x_i$ contains three other points. Are there at least
$$(1+c)\frac{n}{2}$$
distinct distances determined between the $x_i$, for some constant $c>0$ and
all $n$ sufficiently large?

The answer is **no**: as Zach Hunter observed, the regular `n`-gon (`n` points equally spaced on a
circle) is valid and determines only `⌊n/2⌋ < (1+c)n/2` distinct distances, for every `c > 0`.
(In the spirit of related conjectures of Erdős and others, presumably some kind of assumption that
the points are in general position was intended; see `erdos_655.variants.general_position`.) -/
@[category research solved, AMS 5 52]
theorem erdos_655 :
    answer(False) ↔ ∃ c > (0 : ℝ), ∀ᶠ n in atTop, ∀ (X : Finset ℝ²), #X = n → IsValid X →
      (1 + c) * n / 2 ≤ distinctDistances X := by
  show False ↔ _
  refine iff_of_false (fun h => h.elim) ?_
  rintro ⟨c, hc, hev⟩
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  set n := max N 1 with hn
  have hnN : N ≤ n := le_max_left _ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_max_right N 1
  have hP := hN n hnN (ngon n) (ngon_card n) (isValid_ngon n)
  have h1 : (distinctDistances (ngon n) : ℝ) ≤ (n : ℝ) / 2 :=
    le_trans (by exact_mod_cast distinctDistances_ngon_le n) Nat.cast_div_le
  nlinarith [hP, h1, mul_pos hc (lt_of_lt_of_le one_pos hn1)]

/-- Let $x_1,\ldots,x_n\in \mathbb{R}^2$ be such that no circle whose centre is one
of the $x_i$ contains three other points. Are there at least$$(1+c)\frac{n}{2}$$
distinct distances determined between the $x_i$, for some constant $c>0$ and
all $n$ sufficiently large?

In the spirit of related conjectures of Erdős and others, presumably
some kind of assumption that the points are in general position
(e.g. no three on a line and no four on a circle) was intended.-/
@[category research open, AMS 5 52]
theorem erdos_655.variants.general_position :
    answer(sorry) ↔ ∃ c > (0 : ℝ), ∀ᶠ n in atTop, ∀ (X : Finset ℝ²), #X = n → IsValid X →
      InGeneralPosition X → (1 + c) * n / 2 ≤ distinctDistances X := by
  sorry

end Erdos655
