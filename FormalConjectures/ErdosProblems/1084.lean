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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1084

*Reference:* [erdosproblems.com/1084](https://www.erdosproblems.com/1084)

Let `f_2(n)` be the maximum number of pairs of points at distance exactly `1`
among any set of `n` points in `ℝ²`, under the condition that all pairwise
distances are at least `1`.

Estimate the growth of `f_2(n)`.

Status: open.
-/

open Finset Filter Metric Real
open scoped EuclideanGeometry ENNReal

namespace Erdos1084
variable {n : ℕ}

/-- The maximal number of pairs of points which are distance 1 apart that a set of `n` 1-separated
points in `ℝ^d` make. -/
noncomputable def f (d n : ℕ) : ℕ :=
  ⨆ (s : Finset (ℝ^ d)) (_ : s.card = n) (_ : IsSeparated' 1 (s : Set (ℝ^ d))), unitDistNum s

-- TODO: Add erdos_1084.

namespace upper_d1

/- ### Helper lemmas for `erdos_1084.variants.upper_d1`. -/

@[category API, AMS 52]
private lemma dist_one_eq (x y : ℝ^1) : dist x y = |x 0 - y 0| := by
  rw [EuclideanSpace.dist_eq]
  simp [Real.dist_eq, Real.sqrt_sq_eq_abs]

@[category API, AMS 52]
private lemma coord_inj {x y : ℝ^1} (h : x 0 = y 0) : x = y := by
  ext i
  have : i = 0 := Subsingleton.elim _ _
  subst this; exact h

@[category API, AMS 52]
private lemma out_dist_eq_lift {X : Type*} [MetricSpace X] (p : Sym2 X) :
    dist p.out.1 p.out.2 = Sym2.lift ⟨fun a b => dist a b, fun a b => dist_comm a b⟩ p := by
  conv_rhs => rw [← p.out_eq]
  rw [Sym2.lift_mk]

/-- The endpoint of an unordered pair in `ℝ^1` with the larger coordinate. -/
private noncomputable def topPt : Sym2 (ℝ^1) → ℝ^1 :=
  Sym2.lift ⟨fun a b => if a 0 ≤ b 0 then b else a, by
    intro a b
    by_cases h : a 0 ≤ b 0
    · by_cases h2 : b 0 ≤ a 0
      · have : a 0 = b 0 := le_antisymm h h2
        simp [coord_inj this]
      · simp [h, h2]
    · have h2 : b 0 ≤ a 0 := le_of_not_ge h
      simp [h, h2]⟩

@[category API, AMS 52]
private lemma topPt_mk (a b : ℝ^1) : topPt s(a,b) = if a 0 ≤ b 0 then b else a := by
  rw [topPt, Sym2.lift_mk]

@[category API, AMS 52]
private lemma F_elim (s : Finset (ℝ^1)) (p : Sym2 (ℝ^1))
    (hp : p ∈ s.sym2.filter
      (fun p => Sym2.lift ⟨fun a b => dist a b, fun a b => dist_comm a b⟩ p = 1)) :
    ∃ lo hi : ℝ^1, lo ∈ s ∧ hi ∈ s ∧ lo 0 ≤ hi 0 ∧ dist lo hi = 1 ∧ topPt p = hi
      ∧ p = s(lo, hi) := by
  rw [Finset.mem_filter] at hp
  obtain ⟨hmem, hdist⟩ := hp
  induction p with
  | _ a b =>
    rw [Sym2.lift_mk] at hdist
    rw [Finset.mk_mem_sym2_iff] at hmem
    obtain ⟨ha, hb⟩ := hmem
    rw [topPt_mk]
    by_cases h : a 0 ≤ b 0
    · exact ⟨a, b, ha, hb, h, hdist, by simp [h], rfl⟩
    · refine ⟨b, a, hb, ha, le_of_not_ge h, by rw [dist_comm]; exact hdist, by simp [h], ?_⟩
      rw [Sym2.eq_swap]

/-- Upper bound: a 1-separated set of `n` points on the line has at most `n - 1`
pairs at distance exactly `1`. -/
@[category API, AMS 52]
private lemma upper_bound (n : ℕ) (s : Finset (ℝ^1)) (hcard : s.card = n)
    (hsep : IsSeparated' 1 (s : Set (ℝ^1))) : unitDistNum s ≤ n - 1 := by
  rcases eq_or_ne s ∅ with rfl | hne
  · simp [unitDistNum]
  · have hsne : s.Nonempty := nonempty_iff_ne_empty.mpr hne
    obtain ⟨m, hm, hmin⟩ := s.exists_min_image (fun p => p 0) hsne
    set lift1 : Sym2 (ℝ^1) → ℝ := Sym2.lift ⟨fun a b => dist a b, fun a b => dist_comm a b⟩ with hlift
    unfold unitDistNum
    have hfeq : (s.sym2.filter (fun p => dist p.out.1 p.out.2 = 1))
        = s.sym2.filter (fun p => lift1 p = 1) := by
      apply Finset.filter_congr
      intro p _
      rw [out_dist_eq_lift p]
    rw [hfeq]
    set F := s.sym2.filter (fun p => lift1 p = 1) with hF
    have hmaps : ∀ p ∈ F, topPt p ∈ s.erase m := by
      intro p hp
      obtain ⟨lo, hi, hlo, hhi, hle, hd, htop, -⟩ := F_elim s p hp
      rw [htop]
      have hcoord : |lo 0 - hi 0| = 1 := by rw [← dist_one_eq]; exact hd
      have hlolt : lo 0 < hi 0 := by
        rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hcoord with h1 | h1
        · linarith
        · linarith
      have hm_le : (m : ℝ^1) 0 ≤ lo 0 := hmin lo hlo
      refine Finset.mem_erase.mpr ⟨?_, hhi⟩
      intro heq
      rw [heq] at hlolt
      linarith
    have hinj : Set.InjOn topPt F := by
      intro p hp q hq hpq
      rw [Finset.mem_coe] at hp hq
      obtain ⟨lo1, hi1, _, _, hle1, hd1, htop1, hpe⟩ := F_elim s p hp
      obtain ⟨lo2, hi2, _, _, hle2, hd2, htop2, hqe⟩ := F_elim s q hq
      have hhi : hi1 = hi2 := by rw [← htop1, ← htop2]; exact hpq
      have hc1 : |lo1 0 - hi1 0| = 1 := by rw [← dist_one_eq]; exact hd1
      have hc2 : |lo2 0 - hi2 0| = 1 := by rw [← dist_one_eq]; exact hd2
      have hlo1 : lo1 0 = hi1 0 - 1 := by
        rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hc1 with h | h <;> linarith
      have hlo2 : lo2 0 = hi2 0 - 1 := by
        rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hc2 with h | h <;> linarith
      have hlo : lo1 = lo2 := by
        apply coord_inj; rw [hlo1, hlo2, hhi]
      rw [hpe, hqe, hlo, hhi]
    calc F.card ≤ (s.erase m).card := Finset.card_le_card_of_injOn topPt hmaps hinj
    _ = n - 1 := by rw [Finset.card_erase_of_mem hm, hcard]

/- ### Lower bound: the witness `{single 0 0, …, single 0 (n-1)}`. -/

private noncomputable abbrev pt (k : ℕ) : ℝ^1 := EuclideanSpace.single (0:Fin 1) (k:ℝ)

@[category API, AMS 52]
private lemma pt_dist (a b : ℕ) : dist (pt a) (pt b) = |(a:ℝ) - b| := by
  simp only [pt, EuclideanSpace.dist_eq]
  simp [EuclideanSpace.single_apply, Real.sqrt_sq_eq_abs, Real.dist_eq]

@[category API, AMS 52]
private lemma pt_inj : Function.Injective pt := by
  intro a b h
  have := congrArg (fun x => x 0) h
  simp [pt, EuclideanSpace.single_apply] at this
  exact_mod_cast this

private noncomputable def W (n : ℕ) : Finset (ℝ^1) := (Finset.range n).image pt

@[category API, AMS 52]
private lemma W_card (n : ℕ) : (W n).card = n := by
  rw [W, Finset.card_image_of_injective _ pt_inj, Finset.card_range]

@[category API, AMS 52]
private lemma W_sep (n : ℕ) : IsSeparated' 1 ((W n : Finset (ℝ^1)) : Set (ℝ^1)) := by
  intro x hx y hy hxy
  simp only [W, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hx hy
  obtain ⟨a, _, rfl⟩ := hx
  obtain ⟨b, _, rfl⟩ := hy
  have hab : a ≠ b := fun h => hxy (by rw [h])
  rw [edist_dist, show (1:ℝ≥0∞) = ENNReal.ofReal 1 by simp]
  apply ENNReal.ofReal_le_ofReal
  rw [pt_dist]
  rcases Nat.lt_or_ge a b with hlt | hge
  · have hr : (a:ℝ) + 1 ≤ b := by exact_mod_cast hlt
    rw [abs_of_nonpos (by linarith)]; linarith
  · have hgt : b < a := lt_of_le_of_ne hge (Ne.symm hab)
    have hr : (b:ℝ) + 1 ≤ a := by exact_mod_cast hgt
    rw [abs_of_nonneg (by linarith)]; linarith

@[category API, AMS 52]
private lemma lower_count (n : ℕ) : n - 1 ≤ unitDistNum (W n) := by
  unfold unitDistNum
  have key : (Finset.range (n-1)).card ≤
      ((W n).sym2.filter (fun p => dist p.out.1 p.out.2 = 1)).card := by
    apply Finset.card_le_card_of_injOn (fun k => s(pt k, pt (k+1)))
    · intro k hk
      rw [Finset.mem_coe, Finset.mem_range] at hk
      simp only [Finset.mem_coe, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mk_mem_sym2_iff]
        refine ⟨?_, ?_⟩
        · apply Finset.mem_image_of_mem; rw [Finset.mem_range]; omega
        · apply Finset.mem_image_of_mem; rw [Finset.mem_range]; omega
      · rw [out_dist_eq_lift, Sym2.lift_mk]
        show dist (pt k) (pt (k+1)) = 1
        rw [pt_dist]; push_cast; rw [abs_of_nonpos (by linarith)]; ring
    · intro a _ b _ hab
      simp only [Sym2.eq_iff] at hab
      rcases hab with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact pt_inj h1
      · have e1 := pt_inj h1
        have e2 := pt_inj h2
        omega
  rwa [Finset.card_range] at key

@[category API, AMS 52]
private lemma bdd (n : ℕ) : BddAbove (Set.range (fun s : Finset (ℝ^1) =>
    ⨆ (_ : s.card = n) (_ : IsSeparated' 1 (s : Set (ℝ^1))), unitDistNum s)) := by
  refine ⟨n - 1, ?_⟩
  rintro x ⟨s, rfl⟩
  apply ciSup_le'
  intro hc
  apply ciSup_le'
  intro hsep
  exact upper_bound n s hc hsep

end upper_d1

/-- It is easy to check that $f_1(n) = n - 1$. -/
@[category research solved, AMS 52]
theorem erdos_1084.variants.upper_d1 : f 1 n = n - 1 := by
  apply le_antisymm
  · apply ciSup_le'
    intro s
    apply ciSup_le'
    intro hc
    apply ciSup_le'
    intro hsep
    exact upper_d1.upper_bound n s hc hsep
  · refine le_ciSup_of_le (upper_d1.bdd n) (upper_d1.W n) ?_
    have hb1 : BddAbove (Set.range
        (fun _ : IsSeparated' 1 ((upper_d1.W n : Finset (ℝ^1)) : Set (ℝ^1)) =>
        unitDistNum (upper_d1.W n))) := (Set.finite_range _).bddAbove
    have hb2 : BddAbove (Set.range (fun _ : (upper_d1.W n).card = n =>
        ⨆ (_ : IsSeparated' 1 ((upper_d1.W n : Finset (ℝ^1)) : Set (ℝ^1))),
          unitDistNum (upper_d1.W n))) := (Set.finite_range _).bddAbove
    refine le_trans (upper_d1.lower_count n) ?_
    exact le_trans (le_ciSup hb1 (upper_d1.W_sep n)) (le_ciSup hb2 (upper_d1.W_card n))

/-- It is easy to check that $f_2(n) < 3n$. -/
@[category research solved, AMS 52]
theorem erdos_1084.variants.easy_upper_d2 (hn : n ≠ 0) : f 2 n < 3 * n := by
  sorry

/-- Erdős showed that there is some constant $c > 0$ such that $f_2(n) < 3n - c n^{1/2}$. -/
@[category research solved, AMS 52]
theorem erdos_1084.variants.upper_d2 : ∃ c > (0 : ℝ), ∀ n > 0, f 2 n < 3 * n - c * sqrt n := by
  sorry

/-- Erdős conjectured that the triangular lattice is best possible in 2D, in particular that
$f_2(3n^2 + 3n + 1) < 9n^2 + 3n$.

Note: in [Er75f] is read $9n^2 + 6n$, but this seems to be a typo.
-/
@[category research open, AMS 52]
theorem erdos_1084.variants.triangular_optimal_d2 : f 2 (3 * n ^ 2 + 3 * n + 1) = 9 * n ^ 2 + 3 * n := by
  sorry

/-- Erdős claims the existence of two constants $c_1, c_2 > 0$
such that $6n - c_1 n^{2/3} ≤ f_3(n) \le 6n - c_2 n^{2/3}$. -/
@[category research solved, AMS 52]
theorem erdos_1084.variants.upper_lower_d3 :
    ∃ c₁ : ℝ, ∃ c₂ > (0 : ℝ), ∀ᶠ n in atTop,
      6 * n - c₁ * n ^ (2 / 3 : ℝ) ≤ f 3 n ∧ f 3 n ≤ 6 * n - c₂ * n ^ (2 / 3 : ℝ) := by
  sorry

end Erdos1084
