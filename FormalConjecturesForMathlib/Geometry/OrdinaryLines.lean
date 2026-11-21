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

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Ordinary lines and the Sylvester–Gallai theorem

An ordinary line meets a finite point set in exactly two points. Every finite
noncollinear set in a real inner product space has an ordinary line.

The proof uses the minimum positive point-to-line distance argument.

*Reference:* [Mo51] Motzkin, T. S., *The lines and planes connecting the points of a finite set*.
Transactions of the American Mathematical Society 70 (1951), 451–464.
-/

@[expose] public section

namespace SylvesterGallai

open RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private noncomputable def areaSq (u v : V) : ℝ :=
  ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2

private lemma areaSq_nonneg (u v : V) : 0 ≤ areaSq u v := by
  have h := abs_real_inner_le_norm u v
  have := pow_le_pow_left₀ (abs_nonneg ⟪u, v⟫) h 2
  dsimp [areaSq]
  nlinarith [sq_abs ⟪u, v⟫]

private lemma areaSq_comm (u v : V) : areaSq u v = areaSq v u := by
  simp only [areaSq, real_inner_comm v u]
  ring

private lemma areaSq_smul (u v : V) (t : ℝ) :
    areaSq (t • u) v = t ^ 2 * areaSq u v := by
  simp [areaSq, norm_smul, real_inner_smul_left, mul_pow]
  ring

private lemma areaSq_shear (u v : V) (t : ℝ) : areaSq u (v + t • u) = areaSq u v := by
  simp only [areaSq, norm_add_sq_real, inner_add_right, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_self_eq_norm_sq,
    real_inner_comm v u]
  ring

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

private lemma mem_line {a b x : V} :
    x ∈ line[ℝ, a, b] ↔ ∃ t : ℝ, x = a + t • (b - a) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  constructor <;> rintro ⟨t, ht⟩ <;> exact ⟨t, by simpa [add_comm] using ht.symm⟩

private noncomputable def heightSq (p a b : V) : ℝ :=
  areaSq (b - a) (p - a) / ‖b - a‖ ^ 2

private lemma areaSq_pos {p a b : V} (hab : a ≠ b) (hp : p ∉ line[ℝ, a, b]) :
    0 < areaSq (b - a) (p - a) := by
  refine lt_of_le_of_ne (areaSq_nonneg _ _) ?_
  intro h
  obtain ⟨t, ht⟩ := (areaSq_zero_iff (sub_ne_zero.mpr hab.symm)).mp h.symm
  apply hp
  exact mem_line.mpr ⟨t, by rw [← ht]; abel⟩

private lemma off_line {a b p x y : V} (hp : p ∉ line[ℝ, a, b])
    (hx : x ∈ line[ℝ, a, b]) (hy : y ∈ line[ℝ, a, b]) (hxy : x ≠ y) :
    x ∉ line[ℝ, p, y] := by
  intro h
  have hc := collinear_insert_of_mem_affineSpan_pair h
  have hp' : p ∈ line[ℝ, x, y] :=
    hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy
  exact hp ((affineSpan_pair_le_of_mem_of_mem hx hy) hp')

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

namespace EuclideanGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The distinct ordinary lines of a finite point set. The image removes duplicate lines. -/
noncomputable def ordinaryLines (s : Finset V) : Finset (AffineSubspace ℝ V) := by
  classical
  exact (((s ×ˢ s).filter fun p => p.1 ≠ p.2).image
    fun p => line[ℝ, p.1, p.2]).filter fun L => (s.filter fun p => p ∈ L).card = 2

open scoped Classical in
/-- Membership records two distinct points generating a line with exactly two incidences. -/
theorem mem_ordinaryLines {s : Finset V} {L : AffineSubspace ℝ V} :
    L ∈ ordinaryLines s ↔
      (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ line[ℝ, a, b] = L) ∧
        (s.filter fun p => p ∈ L).card = 2 := by
  classical
  simp only [ordinaryLines, Finset.mem_filter, Finset.mem_image, Finset.mem_product]
  aesop

/-- Every line counted by `ordinaryLines` is one-dimensional. -/
theorem isLine_of_mem_ordinaryLines {s : Finset V} {L : AffineSubspace ℝ V}
    (hL : L ∈ ordinaryLines s) : Module.finrank ℝ L.direction = 1 := by
  obtain ⟨⟨a, _, b, _, hab, rfl⟩, _⟩ := mem_ordinaryLines.mp hL
  rw [direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.mpr hab)

/-- The counted lines are precisely the geometric lines meeting the point set in two points. -/
theorem ordinaryLines_eq {s : Finset V} {L : AffineSubspace ℝ V} :
    L ∈ ordinaryLines s ↔
      Module.finrank ℝ L.direction = 1 ∧ ((s : Set V) ∩ (L : Set V)).ncard = 2 := by
  classical
  have hcard : ((s : Set V) ∩ (L : Set V)).ncard =
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
    have : FiniteDimensional ℝ L.direction :=
      FiniteDimensional.of_finrank_pos (by rw [hline]; norm_num)
    have heq : line[ℝ, a, b] = L := by
      apply (AffineSubspace.eq_iff_direction_eq_of_mem
        (left_mem_affineSpan_pair ℝ a b) ha.2).mpr
      apply Submodule.eq_of_le_of_finrank_eq
      · exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem ha.2 hb.2)
      · rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hab)]
        exact hline.symm
    exact mem_ordinaryLines.mpr ⟨⟨a, ha.1, b, hb.1, hab, heq⟩, h⟩

/-- Sylvester–Gallai supplies an ordinary line for every noncollinear finite set. -/
theorem ordinaryLines_nonempty {s : Finset V} (hs : ¬ Collinear ℝ (s : Set V)) :
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

end EuclideanGeometry
