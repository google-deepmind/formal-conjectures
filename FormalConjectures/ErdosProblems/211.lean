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
# Erdős Problem 211

*References:*
- [erdosproblems.com/211](https://www.erdosproblems.com/211)
- [Be83] Beck, József, *On the lattice property of the plane and some problems of Dirac,
  Motzkin and Erdős in combinatorial geometry*. Combinatorica (1983), 281-297.
- [SzTr83] Szemerédi, Endre and Trotter, Jr., William T., *Extremal problems in discrete
  geometry*. Combinatorica (1983), 381-392.
- [Er84] Erdős, P., *Research problems*. Period. Math. Hungar. (1984), 101-103.
- [BGS74] Burr, Stefan A. and Grünbaum, Branko and Sloane, N. J. A., *The orchard problem*.
  Geometriae Dedicata (1974), 397-424.
- [FuPa84] Füredi, Z. and Palásti, I., *Arrangements of lines with a large number of triangles*.
  Proc. Amer. Math. Soc. (1984), 561-566.
-/

@[expose] public section

namespace Erdos211

open EuclideanGeometry Filter

noncomputable local instance (L : AffineSubspace ℝ ℝ²) : DecidablePred (fun p : ℝ² => p ∈ L) :=
  Classical.decPred _

noncomputable local instance : DecidableEq (AffineSubspace ℝ ℝ²) := Classical.decEq _

/-- Distinct lines containing two distinct points of the configuration. -/
noncomputable def determinedLines (s : Finset ℝ²) : Finset (AffineSubspace ℝ ℝ²) := by
  classical
  exact s.offDiag.image fun p => line[ℝ, p.1, p.2]

/-- The uniform Erdős–Beck lower bound. -/
def MainBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n k : ℕ), 1 ≤ k → k < n →
    ∀ s : Finset ℝ², s.card = n →
      (∀ L : AffineSubspace ℝ ℝ², IsLine L → (s.filter fun p => p ∈ L).card ≤ n - k) →
      c * (k : ℝ) * (n : ℝ) ≤ ((determinedLines s).card : ℝ)

/-- The quadratic lower bound for configurations with at most half the points on a line. -/
def QuadraticBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    ∀ s : Finset ℝ², s.card = 2 * n →
      (∀ L : AffineSubspace ℝ ℝ², IsLine L → (s.filter fun p => p ∈ L).card ≤ n) →
      c * (n : ℝ) ^ 2 ≤ ((determinedLines s).card : ℝ)

/-- Erdős speculates that there are at least $(1+o(1))kn/6$ determined lines [Er84].
The asymptotic bound is uniform over $1 \leq k < n$. -/
@[category research open, AMS 5 52]
theorem erdos_211.variants.one_sixth :
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (n k : ℕ), N ≤ n → 1 ≤ k → k < n →
    ∀ s : Finset ℝ², s.card = n →
      (∀ L : AffineSubspace ℝ ℝ², IsLine L → (s.filter fun p => p ∈ L).card ≤ n - k) →
      (1 - ε) / 6 * (k : ℝ) * (n : ℝ) ≤ ((determinedLines s).card : ℝ) := by
  sorry

/-- There are arbitrarily large configurations with no four collinear points and
$\sim n^2/6$ three-point lines, constructed by Burr, Grünbaum, and Sloane [BGS74]
and Füredi and Palásti [FuPa84]. The index need not equal the number of points. -/
@[category research solved, AMS 5 52]
theorem erdos_211.variants.sharpness :
  ∃ s : ℕ → Finset ℝ²,
    Tendsto (fun i => (s i).card) atTop atTop ∧
    (∀ (i : ℕ) (L : AffineSubspace ℝ ℝ²), IsLine L →
      ((s i).filter fun p => p ∈ L).card ≤ 3) ∧
    Tendsto (fun i =>
      (((determinedLines (s i)).filter fun L => ((s i).filter fun p => p ∈ L).card = 3).card : ℝ) /
        ((s i).card : ℝ) ^ 2) atTop (nhds (1 / 6 : ℝ)) := by
  sorry

/-- Membership means that two distinct points of the configuration generate the line. -/
@[category API, AMS 5 52]
theorem mem_determinedLines {s : Finset ℝ²} {L : AffineSubspace ℝ ℝ²} :
    L ∈ determinedLines s ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ line[ℝ, a, b] = L := by
  classical
  simp only [determinedLines, Finset.mem_image, Finset.mem_offDiag]
  aesop

/-- A span of two distinct points is a geometric line. -/
@[category API, AMS 5 52]
theorem isLine_pair {a b : ℝ²} (hab : a ≠ b) : IsLine (line[ℝ, a, b]) := by
  unfold IsLine
  rw [direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.mpr hab)

/-- Two distinct points on a geometric line span the whole line. -/
@[category API, AMS 5 52]
theorem line_pair_eq {a b : ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    line[ℝ, a, b] = L := by
  apply (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ a b) ha).mpr
  apply Submodule.eq_of_le_of_finrank_eq
  · exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem ha hb)
  · exact (isLine_pair hab).trans hL.symm

/-- Every determined line is one-dimensional. -/
@[category API, AMS 5 52]
theorem isLine_of_mem_determinedLines {s : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ determinedLines s) : IsLine L := by
  obtain ⟨a, _, b, _, hab, rfl⟩ := mem_determinedLines.mp hL
  exact isLine_pair hab

/-- The finite image counts precisely all geometric lines containing at least two points. -/
@[category API, AMS 5 52]
theorem determinedLines_eq {s : Finset ℝ²} {L : AffineSubspace ℝ ℝ²} :
    L ∈ determinedLines s ↔ IsLine L ∧ 2 ≤ ((s : Set ℝ²) ∩ (L : Set ℝ²)).ncard := by
  classical
  have hcard : ((s : Set ℝ²) ∩ (L : Set ℝ²)).ncard =
      (s.filter fun p => p ∈ L).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp
  rw [hcard]
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hab, heq⟩ := mem_determinedLines.mp h
    refine ⟨isLine_of_mem_determinedLines h, ?_⟩
    apply Nat.succ_le_iff.mpr
    apply Finset.one_lt_card.mpr
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, heq ▸ left_mem_affineSpan_pair ℝ a b⟩,
      b, Finset.mem_filter.mpr ⟨hb, heq ▸ right_mem_affineSpan_pair ℝ a b⟩, hab⟩
  · rintro ⟨hL, hcard⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (Nat.lt_of_succ_le hcard)
    exact mem_determinedLines.mpr ⟨a, (Finset.mem_filter.mp ha).1,
      b, (Finset.mem_filter.mp hb).1,
      hab, line_pair_eq hL (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab⟩

/-- The fiber over a geometric line consists of the ordered pairs of distinct incident points. -/
@[category API, AMS 5 52]
theorem pair_fiber_eq {s : Finset ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) :
    (s.offDiag.filter fun p => line[ℝ, p.1, p.2] = L) =
      (s.filter fun p => p ∈ L).offDiag := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨ha, hb, hab⟩, heq⟩
    exact ⟨⟨ha, heq ▸ left_mem_affineSpan_pair ℝ p.1 p.2⟩,
      ⟨hb, heq ▸ right_mem_affineSpan_pair ℝ p.1 p.2⟩, hab⟩
  · rintro ⟨⟨ha, haL⟩, ⟨hb, hbL⟩, hab⟩
    exact ⟨⟨ha, hb, hab⟩, line_pair_eq hL haL hbL hab⟩

/-- Exact double counting: each ordered pair belongs to its unique determined line. -/
@[category API, AMS 5 52]
theorem ordered_pair_count (s : Finset ℝ²) :
    s.card * (s.card - 1) = ∑ L ∈ determinedLines s,
      (s.filter fun p => p ∈ L).card * ((s.filter fun p => p ∈ L).card - 1) := by
  classical
  have h := Finset.card_eq_sum_card_image (fun p : ℝ² × ℝ² => line[ℝ, p.1, p.2]) s.offDiag
  have hoff : s.offDiag.card = s.card * (s.card - 1) := by
    rw [Finset.offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hoff] at h
  calc
    s.card * (s.card - 1) = _ := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro L hL
      rw [pair_fiber_eq (isLine_of_mem_determinedLines hL), Finset.offDiag_card]
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]

/-- Elementary bound when no line contains more than $r$ points.
This is weaker than the Erdős–Beck bound and is not a proof of `erdos_211`. -/
@[category API, AMS 5 52]
theorem pair_count_bound {s : Finset ℝ²} {r : ℕ}
    (hr : ∀ L : AffineSubspace ℝ ℝ², IsLine L → (s.filter fun p => p ∈ L).card ≤ r) :
    s.card * (s.card - 1) ≤ (determinedLines s).card * (r * (r - 1)) := by
  classical
  rw [ordered_pair_count]
  calc
    _ ≤ ∑ _L ∈ determinedLines s, r * (r - 1) := by
      apply Finset.sum_le_sum
      intro L hL
      have h := hr L (isLine_of_mem_determinedLines hL)
      exact Nat.mul_le_mul h (Nat.sub_le_sub_right h 1)
    _ = _ := by simp

/-- In a configuration with no three collinear points, every unordered pair gives a line. -/
@[category API, AMS 5 52]
theorem line_count_no_three {s : Finset ℝ²}
    (hs : ∀ L : AffineSubspace ℝ ℝ², IsLine L → (s.filter fun p => p ∈ L).card ≤ 2) :
    s.card * (s.card - 1) = 2 * (determinedLines s).card := by
  classical
  rw [ordered_pair_count]
  calc
    _ = ∑ _L ∈ determinedLines s, 2 := by
      apply Finset.sum_congr rfl
      intro L hL
      have hlo := (determinedLines_eq.mp hL).2
      have hc : ((s : Set ℝ²) ∩ (L : Set ℝ²)).ncard =
          (s.filter fun p => p ∈ L).card := by
        rw [← Set.ncard_coe_finset]
        congr 1
        ext p
        simp
      rw [hc] at hlo
      have heq := Nat.le_antisymm (hs L (isLine_of_mem_determinedLines hL)) hlo
      simp [heq]
    _ = _ := by simp [Nat.mul_comm]

/-- With at most three points on each line, double counting gives the sharp
leading coefficient $1/6$ in a quadratic lower bound. -/
@[category API, AMS 5 52]
theorem six_mul_lines_no_four {s : Finset ℝ²}
    (hs : ∀ L : AffineSubspace ℝ ℝ², IsLine L → (s.filter fun p => p ∈ L).card ≤ 3) :
    s.card * (s.card - 1) ≤ 6 * (determinedLines s).card := by
  simpa [Nat.mul_comm] using pair_count_bound hs

/-- The real-valued form of the preceding bound, including empty configurations. -/
@[category API, AMS 5 52]
theorem real_lower_bound_no_four {s : Finset ℝ²}
    (hs : ∀ L : AffineSubspace ℝ ℝ², IsLine L → (s.filter fun p => p ∈ L).card ≤ 3) :
    (s.card : ℝ) * ((s.card : ℝ) - 1) / 6 ≤ ((determinedLines s).card : ℝ) := by
  have h := six_mul_lines_no_four hs
  by_cases hzero : s.card = 0
  · simp [hzero]
  · have hone : 1 ≤ s.card := by omega
    have hreal : (s.card : ℝ) * ((s.card : ℝ) - 1) ≤
        6 * ((determinedLines s).card : ℝ) := by
      exact_mod_cast h
    linarith

/-- The quadratic special case follows with twice the constant in the main bound. -/
@[category API, AMS 5 52]
theorem quadratic_of_erdos_211 (h : MainBound) : QuadraticBound := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨2 * c, by positivity, ?_⟩
  intro n hn s hs hcap
  have hkn : n < 2 * n := by omega
  have hb := h (2 * n) n hn hkn s hs (by
    intro L hL
    have := hcap L hL
    omega)
  push_cast at hb
  nlinarith

/-- Let $1\leq k<n$. Given $n$ points in $\mathbb{R}^2$, at most $n-k$ on any line,
there are $\gg kn$ many lines which contain at least two points.
Solved by Beck [Be83] and Szemerédi and Trotter [SzTr83]. -/
@[category research solved, AMS 5 52]
@[formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos211.lean#L900"]
theorem erdos_211 : MainBound := by
  sorry

/-- Given any $2n$ points with at most $n$ on a line there are $\gg n^2$ many lines
formed by the points. Solved by Beck [Be83] and Szemerédi and Trotter [SzTr83]. -/
@[category research solved, AMS 5 52]
theorem erdos_211.variants.quadratic : QuadraticBound :=
  quadratic_of_erdos_211 erdos_211

end Erdos211
