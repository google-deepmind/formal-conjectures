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
public import FormalConjectures.ErdosProblems.«466»

/-!
# Erdős Problem 465

*References:*
- [erdosproblems.com/465](https://www.erdosproblems.com/465)
- [Sa76] Sárközy, A., *On distances near integers. I, II*. Studia Sci. Math. Hungar.
  (1976), 37–50, 105–111.
- [Ko01] Konyagin, S. V., *On the distances between points on the plane*. Mat. Zametki
  (2001), 630–633.
- [GM26] Goenka, R. and Moore, K., *Point sets avoiding near-integer distances*.
  [arXiv:2605.06621](https://arxiv.org/abs/2605.06621) (2026).
-/

@[expose] public section

namespace Erdos465

abbrev Point := EuclideanSpace ℝ (Fin 2)


@[category API, AMS 11 52]
theorem distToNearestInt_le (x : ℝ) (z : ℤ) : distToNearestInt x ≤ |x - z| :=
  round_le x z

@[category API, AMS 11 52]
theorem distToNearestInt_ge_iff (x δ : ℝ) :
    δ ≤ distToNearestInt x ↔ ∀ z : ℤ, δ ≤ |x - z| := by
  constructor
  · intro h z
    exact h.trans (distToNearestInt_le x z)
  · intro h
    exact h (round x)

/-- The finite set lies in the disk and every distinct pair avoids integers. -/
def Admissible (X δ : ℝ) (s : Finset Point) : Prop :=
  (∀ p ∈ s, ‖p‖ ≤ X) ∧
  ∀ p ∈ s, ∀ q ∈ s, p ≠ q → δ ≤ distToNearestInt (dist p q)

@[category API, AMS 11 52]
theorem admissible_empty (X δ : ℝ) : Admissible X δ ∅ := by
  simp [Admissible]

@[category API, AMS 11 52]
theorem admissible_singleton {X δ : ℝ} (hX : 0 ≤ X) :
    Admissible X δ {0} := by
  simp [Admissible, hX]

@[category API, AMS 11 52]
theorem admissible_separated {X δ : ℝ} {s : Finset Point}
    (hs : Admissible X δ s) {p q : Point} (hp : p ∈ s) (hq : q ∈ s) (hne : p ≠ q) :
    δ ≤ dist p q := by
  have h := (distToNearestInt_ge_iff (dist p q) δ).mp (hs.2 p hp q hq hne) 0
  simpa using h

@[category API, AMS 11 52]
theorem admissible_mono_radius {X Y δ : ℝ} {s : Finset Point}
    (hs : Admissible X δ s) (hXY : X ≤ Y) : Admissible Y δ s :=
  ⟨fun p hp => (hs.1 p hp).trans hXY, hs.2⟩

@[category API, AMS 11 52]
theorem admissible_mono_delta {X δ η : ℝ} {s : Finset Point}
    (hs : Admissible X δ s) (hηδ : η ≤ δ) : Admissible X η s :=
  ⟨hs.1, fun p hp q hq hne => hηδ.trans (hs.2 p hp q hq hne)⟩

/-- Cardinalities actually realized by admissible configurations. -/
def cardSet (X δ : ℝ) : Set ℕ := {n | ∃ s : Finset Point, Admissible X δ s ∧ s.card = n}

@[category API, AMS 11 52]
theorem cardSet_nonempty (X δ : ℝ) : (cardSet X δ).Nonempty :=
  ⟨0, ∅, admissible_empty X δ, rfl⟩

/-- Compactness supplies a uniform finite cardinality bound when δ>0. -/
@[category API, AMS 11 52]
theorem cardSet_bddAbove (X : ℝ) {δ : ℝ} (hδ : 0 < δ) : BddAbove (cardSet X δ) := by
  classical
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (0 : Point) X).totallyBounded (δ / 2) (by positivity)
  refine ⟨t.ncard, ?_⟩
  rintro n ⟨s, hs, rfl⟩
  have hc : ∀ p : s, ∃ y : t, dist (p : Point) y < δ / 2 := by
    intro p
    have hp : (p : Point) ∈ Metric.closedBall 0 X := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hs.1 p p.property
    have hy := hcover hp
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hy
    obtain ⟨y, hyt, hpy⟩ := hy
    exact ⟨⟨y, hyt⟩, hpy⟩
  choose f hf using hc
  have hinj : Function.Injective f := by
    intro p q hpq
    by_contra hne
    have hne' : (p : Point) ≠ (q : Point) := fun he => hne (Subtype.ext he)
    have hl := admissible_separated hs p.property q.property hne'
    have hu := dist_triangle (p : Point) (f p : Point) (q : Point)
    have hq : dist (f p : Point) q < δ / 2 := by
      rw [dist_comm, hpq]
      exact hf q
    have hp := hf p
    linarith
  let := ht.fintype
  have hh := Fintype.card_le_of_injective f hinj
  simpa [Set.ncard_eq_toFinset_card] using hh

/-- The actual finite maximum for δ>0. Outside that domain this is only a total
extension; every target below explicitly requires δ>0. -/
noncomputable def maximum (X δ : ℝ) : ℕ := sSup (cardSet X δ)

@[category API, AMS 11 52]
theorem maximum_attained (X : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset Point, Admissible X δ s ∧ s.card = maximum X δ :=
  (cardSet_nonempty X δ).csSup_mem (cardSet_bddAbove X hδ).finite

@[category API, AMS 11 52]
theorem card_le_maximum {X δ : ℝ} (hδ : 0 < δ) {s : Finset Point}
    (hs : Admissible X δ s) : s.card ≤ maximum X δ :=
  le_csSup (cardSet_bddAbove X hδ) ⟨s, hs, rfl⟩

@[category API, AMS 11 52]
theorem maximum_mono_radius {X Y δ : ℝ} (hδ : 0 < δ) (hXY : X ≤ Y) :
    maximum X δ ≤ maximum Y δ := by
  obtain ⟨s, hs, he⟩ := maximum_attained X hδ
  rw [← he]
  exact card_le_maximum hδ (admissible_mono_radius hs hXY)

@[category API, AMS 11 52]
theorem maximum_anti_delta (X : ℝ) {δ η : ℝ} (hη : 0 < η) (hηδ : η ≤ δ) :
    maximum X δ ≤ maximum X η := by
  obtain ⟨s, hs, he⟩ := maximum_attained X (hη.trans_le hηδ)
  rw [← he]
  exact card_le_maximum hη (admissible_mono_delta hs hηδ)

/-- Any uniform finite-configuration upper bound is exactly an upper bound on N. -/
@[category API, AMS 11 52]
theorem maximum_le_iff (X : ℝ) {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    maximum X δ ≤ b ↔ ∀ s : Finset Point, Admissible X δ s → s.card ≤ b := by
  constructor
  · intro h s hs
    exact (card_le_maximum hδ hs).trans h
  · intro h
    obtain ⟨s, hs, he⟩ := maximum_attained X hδ
    rw [← he]
    exact h s hs

@[category API, AMS 11 52]
theorem maximum_ge_one {X δ : ℝ} (hX : 0 ≤ X) (hδ : 0 < δ) :
    1 ≤ maximum X δ := by
  simpa using card_le_maximum hδ (admissible_singleton (δ := δ) hX)

@[category API, AMS 11 52]
theorem distToNearestInt_le_half (x : ℝ) : distToNearestInt x ≤ 1 / 2 := by
  unfold distToNearestInt
  rw [abs_le]
  have h1 := sub_half_lt_round x
  have h2 := round_le_add_half x
  constructor <;> linarith

/-- For thresholds above 1/2 at most one point is possible. -/
@[category API, AMS 11 52]
theorem maximum_eq_one_of_half_lt {X δ : ℝ} (hX : 0 ≤ X) (hδ : 1 / 2 < δ) :
    maximum X δ = 1 := by
  have hδ0 : 0 < δ := by linarith
  apply le_antisymm ?_ (maximum_ge_one hX hδ0)
  apply (maximum_le_iff X hδ0 1).mpr
  intro s hs
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra hne
  have hlow := hs.2 p hp q hq hne
  have hupp := distToNearestInt_le_half (dist p q)
  linarith

/-- Translating a configuration to the origin preserves its cardinality and distances. -/
@[category API, AMS 11 52]
theorem card_le_maximum_of_center {X δ : ℝ} (hδ : 0 < δ)
    {c : Point} {s : Finset Point}
    (hs : (s : Set Point) ⊆ Metric.closedBall c X)
    (hpair : (s : Set Point).Pairwise fun p q => δ ≤ distToNearestInt (dist p q)) :
    s.card ≤ maximum X δ := by
  classical
  let f : Point → Point := fun p => p - c
  have hf : Function.Injective f := by
    intro p q h
    simpa [f] using h
  have hd : ∀ p q, dist (f p) (f q) = dist p q := fun p q => by
    simp [f]
  have hadm : Admissible X δ (s.image f) := by
    constructor
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      simpa [f, Metric.mem_closedBall, dist_eq_norm] using hs hq
    · intro p hp q hq hpq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
      have hab : a ≠ b := fun h => hpq (congrArg f h)
      simpa only [hd] using hpair ha hb hab
  rw [← Finset.card_image_of_injective s hf]
  exact card_le_maximum hδ hadm

/-- The attained maximum agrees with the definition shared with Erdős Problem 466. -/
@[category API, AMS 11 52]
theorem maximum_eq_N (X : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    maximum X δ = Erdos466.N X δ := by
  have hb : BddAbove {n | ∃ (c : Point) (s : Finset Point),
      s.card = n ∧ (s : Set Point) ⊆ Metric.closedBall c X ∧
        (s : Set Point).Pairwise fun p q => δ ≤ distToNearestInt (dist p q)} := by
    refine ⟨maximum X δ, ?_⟩
    rintro n ⟨c, s, rfl, hs, hp⟩
    exact card_le_maximum_of_center hδ hs hp
  unfold Erdos466.N
  apply le_antisymm
  · obtain ⟨s, hs, he⟩ := maximum_attained X hδ
    apply le_csSup hb
    refine ⟨0, s, he, ?_, ?_⟩
    · intro p hp
      simpa [Metric.mem_closedBall, dist_zero_right] using hs.1 p hp
    · intro p hp q hq hpq
      exact hs.2 p hp q hq hpq
  · apply csSup_le
    · exact ⟨0, 0, ∅, by simp, by simp, by simp⟩
    · rintro n ⟨c, s, rfl, hs, hp⟩
      exact card_le_maximum_of_center hδ hs hp
/-- Sublinear growth, with the threshold allowed to depend on $\delta$ and $\epsilon$. -/
def SublinearTarget : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ ε : ℝ, 0 < ε →
    ∃ R : ℝ, 0 < R ∧ ∀ X : ℝ, R ≤ X → (maximum X δ : ℝ) < ε * X

/-- Second original question: every positive exponent slack, for each fixed δ>0. -/
def ExponentTarget : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ R : ℝ, 0 < R ∧ ∀ X : ℝ, R ≤ X →
      (maximum X δ : ℝ) < X ^ ((1 : ℝ) / 2 + ε)

/-- Konyagin's square-root estimate for $0<\delta<1/2$. -/
def KonyaginBound : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ C : ℝ, 0 < C ∧
    ∃ R : ℝ, 0 < R ∧ ∀ X : ℝ, R ≤ X → (maximum X δ : ℝ) ≤ C * Real.sqrt X

/-- Extension of the square-root bound to every positive δ. -/
def AllDeltaSquareRootBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
    ∃ R : ℝ, 0 < R ∧ ∀ X : ℝ, R ≤ X → (maximum X δ : ℝ) ≤ C * Real.sqrt X

@[category API, AMS 11 52]
theorem konyagin_to_all_delta (h : KonyaginBound) : AllDeltaSquareRootBound := by
  intro δ hδ
  let η := min δ (1 / 4)
  have hη : 0 < η := lt_min hδ (by norm_num)
  have hη2 : η < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨C, hC, R, hR, hb⟩ := h η hη hη2
  refine ⟨C, hC, R, hR, fun X hX => ?_⟩
  exact (Nat.cast_le.mpr (maximum_anti_delta X hη (min_le_left _ _))).trans (hb X hX)

/-- A square-root upper bound implies sublinear growth. -/
@[category API, AMS 11 52]
theorem squareRoot_implies_sublinear (h : AllDeltaSquareRootBound) : SublinearTarget := by
  intro δ hδ _ ε hε
  obtain ⟨C, hC, R, hR, hb⟩ := h δ hδ
  refine ⟨max R ((C / ε + 1) ^ 2), lt_of_lt_of_le hR (le_max_left _ _), ?_⟩
  intro X hX
  have hRX : R ≤ X := (le_max_left _ _).trans hX
  have hXp : 0 < X := hR.trans_le hRX
  have hsq : (C / ε + 1) ^ 2 ≤ X := (le_max_right _ _).trans hX
  have hq : 0 < C / ε := div_pos hC hε
  have hs : C / ε + 1 ≤ Real.sqrt X := by
    apply (Real.le_sqrt (by positivity) hXp.le).mpr
    exact hsq
  have heq : C / ε * ε = C := div_mul_cancel₀ C (ne_of_gt hε)
  have hlt : C < ε * Real.sqrt X := by nlinarith
  have hspos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXp
  have hm := mul_lt_mul_of_pos_right hlt hspos
  have hss := Real.sq_sqrt hXp.le
  have hbX := hb X hRX
  nlinarith

/-- Conditional analytic reduction to the second original target. -/
@[category API, AMS 11 52]
theorem squareRoot_implies_exponent (h : AllDeltaSquareRootBound) : ExponentTarget := by
  intro δ hδ ε hε
  obtain ⟨C, hC, R, hR, hb⟩ := h δ hδ
  have he : ∀ᶠ X : ℝ in Filter.atTop, C < X ^ ε :=
    (tendsto_rpow_atTop hε).eventually (Filter.eventually_gt_atTop C)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp he
  refine ⟨max R T, lt_of_lt_of_le hR (le_max_left _ _), ?_⟩
  intro X hX
  have hRX := (le_max_left R T).trans hX
  have hTX := (le_max_right R T).trans hX
  have hXp : 0 < X := hR.trans_le hRX
  calc
    (maximum X δ : ℝ) ≤ C * Real.sqrt X := hb X hRX
    _ < X ^ ε * Real.sqrt X := mul_lt_mul_of_pos_right (hT X hTX)
      (Real.sqrt_pos.mpr hXp)
    _ = X ^ ((1 : ℝ) / 2 + ε) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_add hXp]
      ring

/-- Both conclusions follow if the missing analytic estimate is supplied. -/
@[category API, AMS 11 52]
theorem konyagin_implies_full_targets (h : KonyaginBound) :
    SublinearTarget ∧ ExponentTarget :=
  ⟨squareRoot_implies_sublinear (konyagin_to_all_delta h),
    squareRoot_implies_exponent (konyagin_to_all_delta h)⟩

/--
Let $N(X,\delta)$ denote the maximum number of points $P_1,\ldots,P_n$ which can be
chosen in a circle of radius $X$ such that $\|\lvert P_i-P_j\rvert\|\geq\delta$
for all $1\leq i<j\leq n$. Here $\|x\|$ is the distance to the nearest integer.

Is it true that, for any $0<\delta<1/2$, we have $N(X,\delta)=o(X)$?

The first conjecture was proved by Sárközy [Sa76], who in fact proved
$N(X,\delta)\ll\delta^{-3}X/\log\log X$.
-/
@[category research solved, AMS 11 52]
theorem erdos_465.parts.i : answer(True) ↔ SublinearTarget := by
  sorry

/--
In fact, is it true that (for any fixed $\delta>0$) $N(X,\delta)<X^{1/2+o(1)}$?

Konyagin [Ko01] proved the strong upper bound $N(X,\delta)\ll_\delta X^{1/2}$.
-/
@[category research solved, AMS 11 52]
theorem erdos_465.parts.ii : answer(True) ↔ ExponentTarget := by
  sorry

/-- Konyagin [Ko01] proved $N(X,\delta)\ll_\delta X^{1/2}$. -/
@[category research solved, AMS 11 52]
theorem erdos_465.variants.konyagin : KonyaginBound := by
  sorry

end Erdos465