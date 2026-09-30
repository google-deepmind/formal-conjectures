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
# Erdős Problem 102

*Reference:* [erdosproblems.com/102](https://www.erdosproblems.com/102)
-/

@[expose] public section

namespace Erdos102

open EuclideanGeometry Filter

open scoped Classical in
/-- The number of points of `P` that lie on `L`. -/
noncomputable def pointsOn (P : Finset ℝ²) (L : AffineSubspace ℝ ℝ²) : ℕ :=
  (P.filter (· ∈ L)).card

/-- The number of lines that contain more than three points of `P`. -/
noncomputable def richLineCount (P : Finset ℝ²) : ℕ :=
  {L : AffineSubspace ℝ ℝ² | IsLine L ∧ 3 < pointsOn P L}.ncard

/-- `P` has $n$ points and at least $c n^2$ lines that each contain more than three points
of `P`. -/
def Admissible (c : ℝ) (n : ℕ) (P : Finset ℝ²) : Prop :=
  P.card = n ∧ c * (n : ℝ) ^ 2 ≤ richLineCount P

/-- The largest number of points of `P` on a single line. -/
noncomputable def maxCollinear (P : Finset ℝ²) : ℕ :=
  sSup {k : ℕ | ∃ L, IsLine L ∧ pointsOn P L = k}

/-- $h_c(n)$: the minimum of `maxCollinear P` over all admissible `P`. It is `⊤` when no
admissible configuration exists.

Two distinct lines share at most one pair of points, and a line with more than three points of
`P` contains at least $\binom{4}{2} = 6$ pairs. Hence `richLineCount P` $< n^2 / 12$, so for
$c \geq 1/12$ and $n \geq 1$ no configuration is admissible and $h_c(n) = \top$. The problem is
only meaningful for small $c > 0$; the statements below either quantify over all $c > 0$ (where
small $c$ govern the truth value) or restrict to sufficiently small $c$. -/
noncomputable def h (c : ℝ) (n : ℕ) : ℕ∞ :=
  ⨅ (P : Finset ℝ²) (_ : Admissible c n P), (maxCollinear P : ℕ∞)

/-- The plane contains a line. -/
@[category API, AMS 52]
theorem exists_line : ∃ L : AffineSubspace ℝ ℝ², IsLine L := by
  refine ⟨AffineSubspace.mk' 0 (Submodule.span ℝ {EuclideanSpace.single 0 1}), ?_⟩
  unfold IsLine
  rw [AffineSubspace.direction_mk']
  apply finrank_span_singleton
  simp

/-- `M ≤ maxCollinear P` exactly when some line contains at least `M` points of `P`. -/
@[category API, AMS 52]
theorem le_maxCollinear_iff (P : Finset ℝ²) (M : ℕ) :
    M ≤ maxCollinear P ↔ ∃ L, IsLine L ∧ M ≤ pointsOn P L := by
  have hbdd : BddAbove {k : ℕ | ∃ L, IsLine L ∧ pointsOn P L = k} := by
    refine ⟨P.card, ?_⟩
    rintro k ⟨L, -, rfl⟩
    classical
    exact Finset.card_filter_le _ _
  have hne : {k : ℕ | ∃ L, IsLine L ∧ pointsOn P L = k}.Nonempty := by
    obtain ⟨L, hL⟩ := exists_line
    exact ⟨_, L, hL, rfl⟩
  constructor
  · intro hM
    obtain ⟨L, hL, hk⟩ := Nat.sSup_mem hne hbdd
    exact ⟨L, hL, hk ▸ hM⟩
  · rintro ⟨L, hL, hM⟩
    exact hM.trans (le_csSup hbdd ⟨L, hL, rfl⟩)

/-- `M ≤ h c n` exactly when every admissible configuration of $n$ points has a line that
contains at least `M` of its points. -/
@[category API, AMS 52]
theorem le_h_iff (c : ℝ) (n M : ℕ) :
    (M : ℕ∞) ≤ h c n ↔
      ∀ P : Finset ℝ², Admissible c n P → ∃ L, IsLine L ∧ M ≤ pointsOn P L := by
  simp only [h, le_iInf_iff, Nat.cast_le]
  refine forall_congr' fun P => imp_congr_right fun _ => ?_
  exact le_maxCollinear_iff P M

/-- The statement $h_c(n) \to \infty$, written without $h_c$. -/
@[category API, AMS 52]
theorem tendsto_h_iff (c : ℝ) :
    (∀ M : ℕ, ∀ᶠ n in atTop, (M : ℕ∞) ≤ h c n) ↔
      ∀ M : ℕ, ∀ᶠ n in atTop, ∀ P : Finset ℝ², P.card = n →
        c * (n : ℝ) ^ 2 ≤ richLineCount P → ∃ L, IsLine L ∧ M ≤ pointsOn P L := by
  refine forall_congr' fun M => eventually_congr (Eventually.of_forall fun n => ?_)
  rw [le_h_iff]
  exact forall_congr' fun P => ⟨fun hP hcard hrich => hP ⟨hcard, hrich⟩,
    fun hP hadm => hP hadm.1 hadm.2⟩

/--
Let $c > 0$ and let $h_c(n)$ be such that for any $n$ points in $\mathbb{R}^2$ with at least
$cn^2$ lines that each contain more than three of the points, some line contains $h_c(n)$ of
the points. Is it true that, for fixed $c > 0$, $h_c(n) \to \infty$?
-/
@[category research open, question, AMS 52]
theorem erdos_102 :
    ∀ c > 0, ∀ M : ℕ, ∀ᶠ n in atTop, (M : ℕ∞) ≤ h c n := by
  sorry

/--
It is not known whether $h_c(n) \geq 5$ for all sufficiently large $n$.
-/
@[category research open, question, AMS 52]
theorem erdos_102.variants.five :
    ∀ c > 0, ∀ᶠ n in atTop, (5 : ℕ∞) ≤ h c n := by
  sorry

/--
It is easy to see that $h_c(n) \ll_c n^{1/2}$: for all sufficiently small $c > 0$ there are
admissible configurations (e.g. grids) in which no line contains more than $C_c n^{1/2}$ points.
-/
@[category research solved, AMS 52]
theorem erdos_102.variants.upper_sqrt :
    ∃ c₀ > (0 : ℝ), ∀ c ∈ Set.Ioc 0 c₀, ∃ C : ℝ, ∀ᶠ n in atTop,
      h c n ≤ (⌈C * Real.sqrt n⌉₊ : ℕ∞) := by
  sorry

/--
Erdős [Er95] suggested that perhaps $h_c(n) \gg_c n^{1/2}$. Zach Hunter pointed out that this is
false: the points of $\{1, \dots, m\}^d$ with $n \approx m^d$, randomly projected to
$\mathbb{R}^2$, meet every line in $\ll_d n^{1/d}$ points and determine $\gg_d n^2$ lines with
more than three points. This gives $h_c(n) \ll n^{1 / \log(1/c)}$; we state the underlying form:
for every $d \geq 1$ there is $c > 0$ with $h_c(n) \ll_d n^{1/d}$.
-/
@[category research solved, AMS 52]
theorem erdos_102.variants.hunter :
    ∀ d : ℕ, 1 ≤ d → ∃ c > (0 : ℝ), ∃ C : ℝ, ∀ᶠ n in atTop,
      h c n ≤ (⌈C * (n : ℝ) ^ (1 / (d : ℝ))⌉₊ : ℕ∞) := by
  sorry

end Erdos102
