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
# Erdős Problem 210

*References:*
- [erdosproblems.com/210](https://www.erdosproblems.com/210)
- [Mo51] Motzkin, T. S., *The lines and planes connecting the points of a finite set*.
  Transactions of the American Mathematical Society 70 (1951), 451–464.
- [KeMo58] Kelly, L. M. and Moser, W. O. J., *On the number of ordinary lines determined by
  n points*. Canadian Journal of Mathematics 10 (1958), 210–219.
- [CsSa93] Csima, J. and Sawyer, E. T., *There exist 6n/13 ordinary points*.
  Discrete & Computational Geometry 9 (1993), 187–202.
- [GrTa13] Green, B. and Tao, T., *On sets defining few ordinary lines*.
  Discrete & Computational Geometry 50 (2013), 409–468.
-/

@[expose] public section

namespace SylvesterGallai

open RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private noncomputable def areaSq (u v : V) : ℝ :=
  ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2

@[category API, AMS 5 51]
private lemma areaSq_nonneg (u v : V) : 0 ≤ areaSq u v := by
  have h := abs_real_inner_le_norm u v
  have := pow_le_pow_left₀ (abs_nonneg ⟪u, v⟫) h 2
  dsimp [areaSq]
  nlinarith [sq_abs ⟪u, v⟫]

@[category API, AMS 5 51]
private lemma areaSq_comm (u v : V) : areaSq u v = areaSq v u := by
  simp only [areaSq, real_inner_comm v u]
  ring

@[category API, AMS 5 51]
private lemma areaSq_smul (u v : V) (t : ℝ) :
    areaSq (t • u) v = t ^ 2 * areaSq u v := by
  simp [areaSq, norm_smul, real_inner_smul_left, mul_pow]
  ring

@[category API, AMS 5 51]
private lemma areaSq_shear (u v : V) (t : ℝ) : areaSq u (v + t • u) = areaSq u v := by
  simp only [areaSq, norm_add_sq_real, inner_add_right, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_self_eq_norm_sq,
    real_inner_comm v u]
  ring

@[category API, AMS 5 51]
private lemma areaSq_zero_iff {u v : V} (hu : u ≠ 0) :
    areaSq u v = 0 ↔ ∃ t : ℝ, v = t • u := by
  have hn : 0 < ‖u‖ ^ 2 := by positivity
  constructor
  · intro h
    refine ⟨⟪u, v⟫ / ‖u‖ ^ 2, ?_⟩
    have hz : ‖v - (⟪u, v⟫ / ‖u‖ ^ 2) • u‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real]
      simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        real_inner_comm v u]
      dsimp [areaSq] at h
      field_simp
      rw [← real_inner_comm u v] at h
      nlinarith
    have : v - (⟪u, v⟫ / ‖u‖ ^ 2) • u = 0 := by
      exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hz)
    exact sub_eq_zero.mp this
  · rintro ⟨t, rfl⟩
    simp [areaSq, norm_smul, real_inner_smul_right, mul_pow]
    ring

@[category API, AMS 5 51]
private lemma mem_line {a b x : V} :
    x ∈ line[ℝ, a, b] ↔ ∃ t : ℝ, x = a + t • (b - a) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  constructor <;> rintro ⟨t, ht⟩ <;> exact ⟨t, by simpa [add_comm] using ht.symm⟩

private noncomputable def heightSq (p a b : V) : ℝ :=
  areaSq (b - a) (p - a) / ‖b - a‖ ^ 2

@[category API, AMS 5 51]
private lemma areaSq_pos {p a b : V} (hab : a ≠ b) (hp : p ∉ line[ℝ, a, b]) :
    0 < areaSq (b - a) (p - a) := by
  refine lt_of_le_of_ne (areaSq_nonneg _ _) ?_
  intro h
  obtain ⟨t, ht⟩ := (areaSq_zero_iff (sub_ne_zero.mpr hab.symm)).mp h.symm
  apply hp
  exact mem_line.mpr ⟨t, by rw [← ht]; abel⟩

@[category API, AMS 5 51]
private lemma off_line {a b p x y : V} (hp : p ∉ line[ℝ, a, b])
    (hx : x ∈ line[ℝ, a, b]) (hy : y ∈ line[ℝ, a, b]) (hxy : x ≠ y) :
    x ∉ line[ℝ, p, y] := by
  intro h
  have hc := collinear_insert_of_mem_affineSpan_pair h
  have hp' : p ∈ line[ℝ, x, y] :=
    hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy
  exact hp ((affineSpan_pair_le_of_mem_of_mem hx hy) hp')

@[category API, AMS 5 51]
private lemma areaSq_triangle (p x y : V) :
    areaSq (y - p) (x - p) = areaSq (x - y) (p - y) := by
  have h₁ : x - p = (x - y) + (y - p) := by abel
  have h₂ : p - y = -(y - p) := by abel
  rw [h₁]
  have he := areaSq_shear (y - p) (x - y) 1
  simp only [one_smul] at he
  rw [he, areaSq_comm, h₂]
  simp only [areaSq, norm_neg, inner_neg_right, neg_sq]

/-- Kelly's strict inequality for two points on the same side of the perpendicular foot. -/
@[category API, AMS 5 51]
private lemma heightSq_lt {a b p x y : V} (hab : a ≠ b) (hp : p ∉ line[ℝ, a, b])
    (hx : x ∈ line[ℝ, a, b]) (hy : y ∈ line[ℝ, a, b])
    (hs : 0 ≤ ⟪x - p, b - a⟫ * ⟪y - p, b - a⟫)
    (ho : ⟪x - p, b - a⟫ ^ 2 ≤ ⟪y - p, b - a⟫ ^ 2) :
    heightSq x p y < heightSq p a b := by
  obtain ⟨s, hx'⟩ := mem_line.mp hx
  obtain ⟨t, hy'⟩ := mem_line.mp hy
  let v := b - a
  let A := areaSq v (p - a)
  let X := ⟪x - p, v⟫
  let Y := ⟪y - p, v⟫
  have hv : 0 < ‖v‖ ^ 2 := by
    have : v ≠ 0 := sub_ne_zero.mpr hab.symm
    positivity
  have hA : 0 < A := areaSq_pos hab hp
  have hy₀ : y - p ≠ 0 := sub_ne_zero.mpr (fun h => hp (h ▸ hy))
  have hypos : 0 < ‖y - p‖ ^ 2 := by positivity
  have hd : Y - X = (t - s) * ‖v‖ ^ 2 := by
    dsimp [X, Y]
    rw [← inner_sub_left]
    have : y - p - (x - p) = (t - s) • v := by rw [hx', hy']; module
    rw [this, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have ha : areaSq (y - p) (x - p) = (s - t) ^ 2 * A := by
    rw [areaSq_triangle]
    have h₁ : x - y = (s - t) • v := by rw [hx', hy']; module
    have h₂ : p - y = (p - a) + (-t) • v := by rw [hy']; module
    rw [h₁, h₂, areaSq_smul, areaSq_shear]
  have hn : ‖y - p‖ ^ 2 * ‖v‖ ^ 2 = A + Y ^ 2 := by
    have h : areaSq v (y - p) = A := by
      have : y - p = -(p - a) + t • v := by rw [hy']; module
      rw [this, areaSq_shear]
      change areaSq v (-(p - a)) = areaSq v (p - a)
      simp only [areaSq, norm_neg, inner_neg_right, neg_sq]
    dsimp [areaSq, A, Y] at h ⊢
    rw [← real_inner_comm v (y - p)] at h
    linarith
  have hXY : X ^ 2 ≤ X * Y := by
    nlinarith [sq_nonneg (X * Y - X ^ 2)]
  have hstrict : (Y - X) ^ 2 < A + Y ^ 2 := by nlinarith
  rw [heightSq, heightSq, div_lt_div_iff₀ hypos hv]
  have heq : areaSq (y - p) (x - p) * ‖v‖ ^ 2 * ‖v‖ ^ 2 = A * (Y - X) ^ 2 := by
    rw [ha, hd]
    ring
  have hmul := mul_lt_mul_of_pos_left hstrict hA
  rw [← hn, ← heq] at hmul
  nlinarith

@[category API, AMS 5 51]
private lemma same_side_pair (f : Fin 3 → ℝ) :
    ∃ i j, i ≠ j ∧ 0 ≤ f i * f j ∧ (f i) ^ 2 ≤ (f j) ^ 2 := by
  have hsign : 0 ≤ f 0 * f 1 ∨ 0 ≤ f 1 * f 2 ∨ 0 ≤ f 0 * f 2 := by
    rcases le_total 0 (f 0) with h₀ | h₀ <;>
      rcases le_total 0 (f 1) with h₁ | h₁ <;>
        rcases le_total 0 (f 2) with h₂ | h₂ <;>
          first | (left; nlinarith) | (right; left; nlinarith) | (right; right; nlinarith)
  have hpair (i j : Fin 3) (hij : i ≠ j) (hs : 0 ≤ f i * f j) :
      ∃ i j, i ≠ j ∧ 0 ≤ f i * f j ∧ (f i) ^ 2 ≤ (f j) ^ 2 := by
    rcases le_total ((f i) ^ 2) ((f j) ^ 2) with ho | ho
    · exact ⟨i, j, hij, hs, ho⟩
    · exact ⟨j, i, hij.symm, by simpa [mul_comm] using hs, ho⟩
  rcases hsign with h | h | h
  · exact hpair 0 1 (by decide) h
  · exact hpair 1 2 (by decide) h
  · exact hpair 0 2 (by decide) h

@[category API, AMS 5 51]
private lemma exists_off_line (s : Finset V) (hs : ¬ Collinear ℝ (s : Set V)) :
    ∃ p ∈ s, ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ p ∉ line[ℝ, a, b] := by
  classical
  by_contra! h
  apply hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simpa using collinear_empty ℝ V
  by_cases hall : ∀ b ∈ s, b = a
  · exact (collinear_singleton ℝ a).subset (by simpa using hall)
  push Not at hall
  obtain ⟨b, hb, hba⟩ := hall
  rw [collinear_iff_of_mem ha]
  refine ⟨b - a, ?_⟩
  intro p hp
  obtain ⟨t, ht⟩ := mem_line.mp (h p hp a ha b hb hba.symm)
  exact ⟨t, by simpa [vadd_eq_add, add_comm] using ht⟩

/-- A finite noncollinear subset of a real inner product space has an ordinary line. -/
@[category API, AMS 5 51]
theorem exists_ordinary_line (s : Finset V) (hs : ¬ Collinear ℝ (s : Set V)) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∀ p ∈ s, p ∈ line[ℝ, a, b] → p = a ∨ p = b := by
  classical
  let T := (s ×ˢ s ×ˢ s).filter
    (fun q : V × V × V => q.2.1 ≠ q.2.2 ∧ q.1 ∉ line[ℝ, q.2.1, q.2.2])
  have hT (p a b : V) : (p, a, b) ∈ T ↔
      p ∈ s ∧ a ∈ s ∧ b ∈ s ∧ a ≠ b ∧ p ∉ line[ℝ, a, b] := by
    simp [T, and_assoc]
  obtain ⟨p, hp, a, ha, b, hb, hab, hpab⟩ := exists_off_line s hs
  have hne : T.Nonempty := ⟨(p, a, b), (hT p a b).mpr ⟨hp, ha, hb, hab, hpab⟩⟩
  obtain ⟨⟨p, a, b⟩, hmem, hmin⟩ :=
    T.exists_min_image (fun q => heightSq q.1 q.2.1 q.2.2) hne
  obtain ⟨hp, ha, hb, hab, hpab⟩ := (hT p a b).mp hmem
  refine ⟨a, ha, b, hb, hab, ?_⟩
  intro c hc hcL
  by_contra! h
  let q : Fin 3 → V := ![a, b, c]
  have hqS (i) : q i ∈ s := by fin_cases i <;> assumption
  have hqL (i) : q i ∈ line[ℝ, a, b] := by
    fin_cases i
    · exact left_mem_affineSpan_pair ℝ a b
    · exact right_mem_affineSpan_pair ℝ a b
    · exact hcL
  have hq : Function.Injective q := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [q]
  let f : Fin 3 → ℝ := fun i => ⟪q i - p, b - a⟫
  obtain ⟨i, j, hij, hsign, horder⟩ := same_side_pair f
  have hpj : p ≠ q j := fun he => hpab (he ▸ hqL j)
  have hnew : (q i, p, q j) ∈ T := (hT _ _ _).mpr
    ⟨hqS i, hp, hqS j, hpj, off_line hpab (hqL i) (hqL j) (fun he => hij (hq he))⟩
  exact (not_lt_of_ge (hmin _ hnew))
    (heightSq_lt hab hpab (hqL i) (hqL j) hsign horder)

end SylvesterGallai

namespace Erdos210

open EuclideanGeometry Filter

/-- The distinct ordinary lines of a finite point set. The image removes duplicate lines. -/
noncomputable def ordinaryLines (s : Finset ℝ²) : Finset (AffineSubspace ℝ ℝ²) := by
  classical
  exact (((s ×ˢ s).filter fun p => p.1 ≠ p.2).image
    fun p => line[ℝ, p.1, p.2]).filter fun L => (s.filter fun p => p ∈ L).card = 2

/-- The sharp ordinary-line guarantee for noncollinear sets of $n$ points.
For $n<3$, there are no such configurations, and the infimum is $0$. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ s : Finset ℝ²,
    s.card = n ∧ ¬ Collinear ℝ (s : Set ℝ²) ∧ (ordinaryLines s).card = m}

/-- Let $f(n)$ be the sharp guarantee such that, for any $n$ points in $\mathbb R^2$,
not all on a line, there are at least $f(n)$ lines which contain exactly two points
(called ordinary lines). Does $f(n)\to\infty$?
That $f(n)\to\infty$ was proved by Motzkin [Mo51]. -/
@[category research solved, AMS 5 51]
theorem erdos_210.parts.i : answer(True) ↔ Tendsto f atTop atTop := by
  sorry

/-- Kelly and Moser [KeMo58] proved that $f(n)\geq 3n/7$ for all $n$.
Only $n\geq3$ have noncollinear configurations. -/
@[category research solved, AMS 5 51]
theorem erdos_210.lower_bound : ∀ n : ℕ, 3 ≤ n → 3 * n ≤ 7 * f n := by
  sorry

/-- Csima and Sawyer [CsSa93] proved $f(n)\geq6n/13$ when $n\geq8$. -/
@[category research solved, AMS 5 51]
theorem erdos_210.variants.csima_sawyer : ∀ n : ℕ, 8 ≤ n → 6 * n ≤ 13 * f n := by
  sorry

/-- Green and Tao [GrTa13] proved $f(n)\geq n/2$ for sufficiently large $n$. -/
@[category research solved, AMS 5 51]
theorem erdos_210.variants.green_tao : ∀ᶠ n : ℕ in atTop, n ≤ 2 * f n := by
  sorry

/-- Green and Tao [GrTa13] proved $f(n)\geq3\lfloor n/4\rfloor$ for sufficiently
large odd $n$ [GrTa13, Theorem 2.2]. -/
@[category research solved, AMS 5 51]
theorem erdos_210.variants.green_tao_odd :
    ∀ᶠ n : ℕ in atTop, Odd n → 3 * (n / 4) ≤ f n := by
  sorry

/-- Green and Tao [GrTa13, Proposition 2.1] give configurations attaining $n/2$
ordinary lines for sufficiently large even $n$. -/
@[category research solved, AMS 5 51]
theorem erdos_210.variants.even_upper_bound :
    ∀ᶠ n : ℕ in atTop, Even n → 2 * f n ≤ n := by
  sorry

/-- Kelly and Moser [KeMo58] give a seven-point configuration with three ordinary
lines, attaining their lower bound at $n=7$. -/
@[category research solved, AMS 5 51]
theorem erdos_210.variants.seven : f 7 = 3 := by
  sorry

open scoped Classical in
/-- Membership records two distinct points generating a line with exactly two incidences. -/
@[category API, AMS 5 51]
theorem mem_ordinaryLines {s : Finset ℝ²} {L : AffineSubspace ℝ ℝ²} :
    L ∈ ordinaryLines s ↔
      (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ line[ℝ, a, b] = L) ∧
        (s.filter fun p => p ∈ L).card = 2 := by
  classical
  simp only [ordinaryLines, Finset.mem_filter, Finset.mem_image, Finset.mem_product]
  aesop

/-- Every line counted by `ordinaryLines` is one-dimensional. -/
@[category API, AMS 5 51]
theorem isLine_of_mem_ordinaryLines {s : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ ordinaryLines s) : IsLine L := by
  obtain ⟨⟨a, _, b, _, hab, rfl⟩, _⟩ := mem_ordinaryLines.mp hL
  unfold IsLine
  rw [direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.mpr hab)

/-- The counted lines are precisely the geometric lines meeting the point set in two points. -/
@[category API, AMS 5 51]
theorem ordinaryLines_eq {s : Finset ℝ²} {L : AffineSubspace ℝ ℝ²} :
    L ∈ ordinaryLines s ↔ IsLine L ∧ ((s : Set ℝ²) ∩ (L : Set ℝ²)).ncard = 2 := by
  classical
  have hcard : ((s : Set ℝ²) ∩ (L : Set ℝ²)).ncard =
      (s.filter fun p => p ∈ L).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp
  rw [hcard]
  constructor
  · exact fun h => ⟨isLine_of_mem_ordinaryLines h, (mem_ordinaryLines.mp h).2⟩
  · rintro ⟨hline, h⟩
    obtain ⟨a, b, hab, habs⟩ := Finset.card_eq_two.mp h
    have ha : a ∈ s ∧ a ∈ L := by
      have : a ∈ s.filter fun p => p ∈ L := by rw [habs]; simp
      exact Finset.mem_filter.mp this
    have hb : b ∈ s ∧ b ∈ L := by
      have : b ∈ s.filter fun p => p ∈ L := by rw [habs]; simp
      exact Finset.mem_filter.mp this
    have heq : line[ℝ, a, b] = L := by
      apply (AffineSubspace.eq_iff_direction_eq_of_mem
        (left_mem_affineSpan_pair ℝ a b) ha.2).mpr
      apply Submodule.eq_of_le_of_finrank_eq
      · exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem ha.2 hb.2)
      · rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hab)]
        exact hline.symm
    exact mem_ordinaryLines.mpr ⟨⟨a, ha.1, b, hb.1, hab, heq⟩, h⟩

/-- Sylvester–Gallai supplies an ordinary line for every noncollinear finite set. -/
@[category API, AMS 5 51]
theorem ordinaryLines_nonempty {s : Finset ℝ²} (hs : ¬ Collinear ℝ (s : Set ℝ²)) :
    (ordinaryLines s).Nonempty := by
  classical
  obtain ⟨a, ha, b, hb, hab, h⟩ := SylvesterGallai.exists_ordinary_line s hs
  refine ⟨line[ℝ, a, b], mem_ordinaryLines.mpr ⟨⟨a, ha, b, hb, hab, rfl⟩, ?_⟩⟩
  have heq : (s.filter fun p => p ∈ line[ℝ, a, b]) = {a, b} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun hp => h p hp.1 hp.2
    · intro hp
      rcases hp with hp | hp
      · subst p
        exact ⟨ha, left_mem_affineSpan_pair ℝ a b⟩
      · subst p
        exact ⟨hb, right_mem_affineSpan_pair ℝ a b⟩
  simp [heq, hab]

/-- A configuration bounds the sharp guarantee from above. -/
@[category API, AMS 5 51]
theorem f_le {n : ℕ} {s : Finset ℝ²} (hn : s.card = n)
    (hs : ¬ Collinear ℝ (s : Set ℝ²)) : f n ≤ (ordinaryLines s).card :=
  csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ⟨s, hn, hs, rfl⟩

/-- A right triangle is noncollinear. -/
@[category API, AMS 5 51]
theorem triangle_not_collinear :
    ¬ Collinear ℝ ({!₂[(0 : ℝ), 0], !₂[(1 : ℝ), 0], !₂[(0 : ℝ), 1]} : Set ℝ²) := by
  intro h
  have heq : (!₂[(0 : ℝ), 0] : ℝ²) ≠ !₂[(1 : ℝ), 0] := by
    intro he
    have := congrArg (fun p : ℝ² => p 0) he
    norm_num at this
  have hm : (!₂[(0 : ℝ), 1] : ℝ²) ∈ line[ℝ, !₂[(0 : ℝ), 0], !₂[(1 : ℝ), 0]] :=
    h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) heq
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hm
  have := congrArg (fun p : ℝ² => p 1) ht
  norm_num [AffineMap.lineMap_apply] at this

/-- Every cardinality at least three has a noncollinear configuration. -/
@[category API, AMS 5 51]
theorem exists_configuration {n : ℕ} (hn : 3 ≤ n) :
    ∃ s : Finset ℝ², s.card = n ∧ ¬ Collinear ℝ (s : Set ℝ²) := by
  classical
  let t : Finset ℝ² := {!₂[(0 : ℝ), 0], !₂[(1 : ℝ), 0], !₂[(0 : ℝ), 1]}
  have ht : t.card ≤ n := by
    calc
      t.card ≤ 3 := Finset.card_le_three
      _ ≤ n := hn
  obtain ⟨s, hts, hsn⟩ := Infinite.exists_superset_card_eq t n ht
  refine ⟨s, hsn, fun hs => triangle_not_collinear (hs.subset ?_)⟩
  intro p hp
  apply hts
  simpa [t] using hp

/-- The infimum defining $f(n)$ is attained when $n\geq3$. -/
@[category API, AMS 5 51]
theorem f_attained {n : ℕ} (hn : 3 ≤ n) :
    ∃ s : Finset ℝ², s.card = n ∧ ¬ Collinear ℝ (s : Set ℝ²) ∧
      (ordinaryLines s).card = f n := by
  obtain ⟨s, hs, hcol⟩ := exists_configuration hn
  apply csInf_mem (s := {m : ℕ | ∃ s : Finset ℝ²,
    s.card = n ∧ ¬ Collinear ℝ (s : Set ℝ²) ∧ (ordinaryLines s).card = m})
  exact ⟨(ordinaryLines s).card, s, hs, hcol, rfl⟩

/-- The infimum is exactly the largest uniform lower bound over all configurations. -/
@[category API, AMS 5 51]
theorem le_f_iff {n m : ℕ} (hn : 3 ≤ n) :
    m ≤ f n ↔ ∀ s : Finset ℝ², s.card = n → ¬ Collinear ℝ (s : Set ℝ²) →
      m ≤ (ordinaryLines s).card := by
  constructor
  · exact fun h s hs hc => h.trans (f_le hs hc)
  · intro h
    obtain ⟨s, hs, hc, hcard⟩ := f_attained hn
    simpa [hcard] using h s hs hc

/-- The Sylvester–Gallai theorem states that $f(n)\geq1$. -/
@[category research solved, AMS 5 51]
theorem erdos_210.variants.sylvester_gallai {n : ℕ} (hn : 3 ≤ n) : 1 ≤ f n := by
  apply (le_f_iff hn).mpr
  intro s _ hs
  exact (ordinaryLines_nonempty hs).card_pos

/-- The bound of Kelly–Moser implies the positive answer to the divergence question. -/
@[category API, AMS 5 51]
theorem tendsto_of_kelly_moser (h : ∀ n : ℕ, 3 ≤ n → 3 * n ≤ 7 * f n) :
    Tendsto f atTop atTop := by
  apply tendsto_atTop.mpr
  intro m
  filter_upwards [eventually_ge_atTop (max 3 (7 * m))] with n hn
  have hbound := h n (le_trans (le_max_left _ _) hn)
  have hn' := le_trans (le_max_right _ _) hn
  omega

/-- The sufficiently-large $n/2$ bound implies divergence. -/
@[category API, AMS 5 51]
theorem tendsto_of_green_tao (h : ∀ᶠ n : ℕ in atTop, n ≤ 2 * f n) : Tendsto f atTop atTop := by
  apply tendsto_atTop.mpr
  intro m
  filter_upwards [h, eventually_ge_atTop (2 * m)] with n hn hm
  omega

/-- Points used for a configuration with all but one point on a single line. -/
def axisPoint (i : ℕ) : ℝ² := !₂[(i : ℝ), 0]

/-- The point off that line. -/
def apex : ℝ² := !₂[(0 : ℝ), 1]

/-- The near-pencil configuration consists of $n-1$ points on the horizontal axis and an apex. -/
noncomputable def nearPencil (n : ℕ) : Finset ℝ² := by
  classical
  exact insert apex ((Finset.range (n - 1)).image axisPoint)

/-- Distinct indices give distinct axis points. -/
@[category API, AMS 5 51]
theorem axisPoint_injective : Function.Injective axisPoint := by
  intro i j h
  have := congrArg (fun p : ℝ² => p 0) h
  simpa [axisPoint] using this

/-- The apex is distinct from every axis point. -/
@[category API, AMS 5 51]
theorem apex_ne_axisPoint (i : ℕ) : apex ≠ axisPoint i := by
  intro h
  have := congrArg (fun p : ℝ² => p 1) h
  norm_num [apex, axisPoint] at this

/-- Each axis point is on the horizontal line. -/
@[category API, AMS 5 51]
theorem axisPoint_mem (i : ℕ) : axisPoint i ∈ line[ℝ, axisPoint 0, axisPoint 1] := by
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨(i : ℝ), ?_⟩
  ext j
  fin_cases j <;> simp [axisPoint, AffineMap.lineMap_apply]

/-- The near-pencil construction has the requested cardinality. -/
@[category API, AMS 5 51]
theorem nearPencil_card {n : ℕ} (hn : 1 ≤ n) : (nearPencil n).card = n := by
  classical
  have hap : apex ∉ (Finset.range (n - 1)).image axisPoint := by
    simp only [Finset.mem_image]
    rintro ⟨i, _, hi⟩
    exact apex_ne_axisPoint i hi.symm
  rw [nearPencil, Finset.card_insert_of_notMem hap, Finset.card_image_of_injective _
    axisPoint_injective, Finset.card_range]
  omega

/-- For $n\geq3$, the near-pencil construction contains a noncollinear triangle. -/
@[category API, AMS 5 51]
theorem nearPencil_not_collinear {n : ℕ} (hn : 3 ≤ n) :
    ¬ Collinear ℝ (nearPencil n : Set ℝ²) := by
  classical
  intro h
  apply triangle_not_collinear
  apply h.subset
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  have haxis (i : ℕ) (hi : i < n - 1) : axisPoint i ∈ nearPencil n := by
    simp only [nearPencil, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  rcases hp with rfl | rfl | rfl
  · simpa [axisPoint] using haxis 0 (by omega)
  · simpa [axisPoint] using haxis 1 (by omega)
  · change apex ∈ nearPencil n
    simp [nearPencil]

open scoped Classical in
/-- Every ordinary line of a near-pencil is either horizontal or joins an axis point to the apex. -/
@[category API, AMS 5 51]
theorem ordinaryLines_nearPencil_subset (n : ℕ) :
    ordinaryLines (nearPencil n) ⊆
      insert (line[ℝ, axisPoint 0, axisPoint 1])
        (((Finset.range (n - 1)).image axisPoint).image fun p => line[ℝ, apex, p]) := by
  intro L hL
  obtain ⟨⟨a, ha, b, hb, hab, rfl⟩, _⟩ := mem_ordinaryLines.mp hL
  simp only [nearPencil, Finset.mem_insert] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact (hab rfl).elim
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  · rcases hb with rfl | hb
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨a, ha, AffineSubspace.affineSpan_pair_comm⟩)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      have heq := affineSpan_pair_eq_of_mem_of_mem_of_ne
        (axisPoint_mem i) (axisPoint_mem j) hab
      exact Finset.mem_insert.mpr (Or.inl heq)

/-- The near-pencil construction has at most $n$ ordinary lines. -/
@[category API, AMS 5 51]
theorem ordinaryLines_nearPencil_le {n : ℕ} (hn : 1 ≤ n) :
    (ordinaryLines (nearPencil n)).card ≤ n := by
  classical
  calc
    (ordinaryLines (nearPencil n)).card ≤ _ := Finset.card_le_card (ordinaryLines_nearPencil_subset n)
    _ ≤ (((Finset.range (n - 1)).image axisPoint).image
      fun p => line[ℝ, apex, p]).card + 1 := Finset.card_insert_le _ _
    _ ≤ ((Finset.range (n - 1)).image axisPoint).card + 1 :=
      Nat.add_le_add_right Finset.card_image_le 1
    _ ≤ (Finset.range (n - 1)).card + 1 := Nat.add_le_add_right Finset.card_image_le 1
    _ = n := by rw [Finset.card_range]; omega

/-- An explicit near-pencil gives the linear upper bound $f(n)\leq n$. -/
@[category research solved, AMS 5 51]
theorem erdos_210.upper_bound {n : ℕ} (hn : 3 ≤ n) : f n ≤ n :=
  (f_le (nearPencil_card (by omega)) (nearPencil_not_collinear hn)).trans
    (ordinaryLines_nearPencil_le (by omega))

/-- How fast does $f(n)$ tend to infinity? Kelly–Moser [KeMo58] and the near-pencil
construction show that its growth is linear. -/
@[category research solved, AMS 5 51]
theorem erdos_210.parts.ii :
    (fun n : ℕ => (f n : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
  sorry

/-- The proved upper bound is the upper half of the linear-growth assertion. -/
@[category API, AMS 5 51]
theorem f_isBigO : (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 3] with n hn
  simpa using (Nat.cast_le.mpr (erdos_210.upper_bound hn) : (f n : ℝ) ≤ (n : ℝ))

/-- Kelly–Moser and the explicit upper construction together imply linear growth. -/
@[category API, AMS 5 51]
theorem linear_growth_of_kelly_moser (h : ∀ n : ℕ, 3 ≤ n → 3 * n ≤ 7 * f n) :
    (fun n : ℕ => (f n : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine ⟨f_isBigO, Asymptotics.IsBigO.of_bound 7 ?_⟩
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hb := h n hn
  have hb' : n ≤ 7 * f n := by omega
  have hr : (n : ℝ) ≤ 7 * (f n : ℝ) := by exact_mod_cast hb'
  simpa using hr

/-- The Green–Tao bound likewise implies linear growth. -/
@[category API, AMS 5 51]
theorem linear_growth_of_green_tao (h : ∀ᶠ n : ℕ in atTop, n ≤ 2 * f n) :
    (fun n : ℕ => (f n : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine ⟨f_isBigO, Asymptotics.IsBigO.of_bound 2 ?_⟩
  filter_upwards [h] with n hn
  have hr : (n : ℝ) ≤ 2 * (f n : ℝ) := by exact_mod_cast hn
  simpa using hr

/-- Fewer than three points are collinear. -/
@[category API, AMS 5 51]
theorem collinear_of_card_lt_three {s : Finset ℝ²} (hs : s.card < 3) :
    Collinear ℝ (s : Set ℝ²) := by
  classical
  have hc : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  rcases hc with hc | hc | hc
  · have he : s = ∅ := Finset.card_eq_zero.mp hc
    simpa [he] using collinear_empty ℝ ℝ²
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    simpa using collinear_singleton ℝ a
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp hc
    simpa using collinear_pair ℝ a b

/-- The definition uses the default value zero where no noncollinear configuration exists. -/
@[category API, AMS 5 51]
theorem f_eq_zero_of_lt_three {n : ℕ} (hn : n < 3) : f n = 0 := by
  have he : {m : ℕ | ∃ s : Finset ℝ²,
      s.card = n ∧ ¬ Collinear ℝ (s : Set ℝ²) ∧ (ordinaryLines s).card = m} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro m ⟨s, hs, hc, _⟩
    exact hc (collinear_of_card_lt_three (by omega))
  simp [f, he]

/-- Kelly–Moser's extremal-function formulation is equivalent to its configuration formulation. -/
@[category API, AMS 5 51]
theorem kelly_moser_iff : (∀ n : ℕ, 3 ≤ n → 3 * n ≤ 7 * f n) ↔
    ∀ s : Finset ℝ², ¬ Collinear ℝ (s : Set ℝ²) →
      3 * s.card ≤ 7 * (ordinaryLines s).card := by
  constructor
  · intro h s hs
    have hn : 3 ≤ s.card := by
      by_contra! hn
      exact hs (collinear_of_card_lt_three hn)
    exact (h s.card hn).trans (Nat.mul_le_mul_left 7 (f_le rfl hs))
  · intro h n hn
    obtain ⟨s, hs, hc, hf⟩ := f_attained hn
    simpa [hs, hf] using h s hc

/-- The eventual Green–Tao bound has a single threshold uniform over all configurations. -/
@[category API, AMS 5 51]
theorem green_tao_iff : (∀ᶠ n : ℕ in atTop, n ≤ 2 * f n) ↔
    ∃ N : ℕ, 3 ≤ N ∧ ∀ s : Finset ℝ², N ≤ s.card →
      ¬ Collinear ℝ (s : Set ℝ²) → s.card ≤ 2 * (ordinaryLines s).card := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    refine ⟨max 3 N, le_max_left _ _, ?_⟩
    intro s hs hc
    exact (hN s.card ((le_max_right _ _).trans hs)).trans
      (Nat.mul_le_mul_left 2 (f_le rfl hc))
  · rintro ⟨N, hN, h⟩
    apply eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨s, hs, hc, hf⟩ := f_attained (hN.trans hn)
    simpa [hs, hf] using h s (by simpa [hs] using hn) hc

/-- A sharp extremal guarantee is uniquely characterized by uniform validity and attainment. -/
@[category API, AMS 5 51]
theorem f_unique {n m : ℕ} (hn : 3 ≤ n)
    (hlower : ∀ s : Finset ℝ², s.card = n → ¬ Collinear ℝ (s : Set ℝ²) →
      m ≤ (ordinaryLines s).card)
    (hattain : ∃ s : Finset ℝ², s.card = n ∧ ¬ Collinear ℝ (s : Set ℝ²) ∧
      (ordinaryLines s).card = m) : m = f n := by
  apply Nat.le_antisymm ((le_f_iff hn).mpr hlower)
  obtain ⟨s, hs, hc, hm⟩ := hattain
  simpa [hm] using f_le hs hc

/-- The two sharp eventual bounds imply the exact value on sufficiently large even inputs. -/
@[category API, AMS 5 51]
theorem eventually_even_exact
    (hl : ∀ᶠ n : ℕ in atTop, n ≤ 2 * f n)
    (hu : ∀ᶠ n : ℕ in atTop, Even n → 2 * f n ≤ n) :
    ∀ᶠ n : ℕ in atTop, Even n → 2 * f n = n := by
  filter_upwards [hl, hu] with n hl hu
  intro hn
  exact Nat.le_antisymm (hu hn) hl

end Erdos210
