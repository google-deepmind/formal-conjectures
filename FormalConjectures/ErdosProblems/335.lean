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
# Erdős Problem 335

Definitions and statements for the density-equality question, with a countable-null
circle construction and periodic examples. These examples do not characterize all pairs.

Source: T. F. Bloom, *Erdős Problem #335*, https://www.erdosproblems.com/335
originally [ErGr80, p. 51].

> Let `d(A)` denote the density of `A ⊆ ℕ`. Characterise those `A, B ⊆ ℕ` with positive
> density such that `d(A + B) = d(A) + d(B)`.

Conventions, following the paper the problem page cites
(E. Ackelsberg, F. K. Richter, *An inverse theorem for sumsets of sets of positive density
in the integers*, arXiv:2604.12864v1, 14 Apr 2026):

* `ℕ = {1, 2, 3, …}`. We use Lean's `ℕ` (which contains `0`) and require explicitly that
  the sets do not contain `0` (`A ⊆ Set.Ioi 0`). This matters: if `0 ∈ A` then `B ⊆ A + B`.
* `d(A) = lim_{N → ∞} |A ∩ [N]| / N` with `[N] = {1, …, N}`, and "`A` has density `δ`" means
  that this limit **exists** and equals `δ`.  In `d(A + B) = d(A) + d(B)` the density of
  `A + B` is likewise required to exist.
-/

@[expose] public section

open Filter Topology MeasureTheory
open scoped Pointwise

namespace Erdos335

/-- `count A N = |A ∩ {1, …, N}|`. -/
noncomputable def count (A : Set ℕ) (N : ℕ) : ℕ := by
  classical exact ((Finset.Icc 1 N).filter (· ∈ A)).card

/-- `A` has natural density `δ`: `|A ∩ [N]| / N → δ` as `N → ∞` (the limit exists). -/
def HasDensity (A : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (count A N : ℝ) / N) atTop (𝓝 δ)

/-- Density along a sequence `Ns → ∞`: `d_N(A) = lim_s |A ∩ [N_s]| / N_s` exists and is `δ`. -/
def HasDensityAlong (Ns : ℕ → ℕ) (A : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun s : ℕ => (count A (Ns s) : ℝ) / (Ns s)) atTop (𝓝 δ)

/-- The pairs that Erdős Problem #335 asks to characterise: `A, B ⊆ {1,2,…}`, both with
positive (existing) density, such that `A + B` has density `d(A) + d(B)`. -/
def IsErdos335Pair (A B : Set ℕ) : Prop :=
  A ⊆ Set.Ioi 0 ∧ B ⊆ Set.Ioi 0 ∧
    ∃ dA dB : ℝ, 0 < dA ∧ 0 < dB ∧ HasDensity A dA ∧ HasDensity B dB ∧
      HasDensity (A + B) (dA + dB)

/-- The circle `ℝ/ℤ`. -/
abbrev Circle1 : Type := AddCircle (1 : ℝ)

instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The point `{nθ} ∈ ℝ/ℤ`: the class of `nθ` modulo `1` (equivalently of its fractional part). -/
noncomputable def rot (θ : ℝ) (n : ℕ) : Circle1 := ((n * θ : ℝ) : Circle1)

/-- **The construction on the problem page, read literally.** There is `θ > 0` and
`X_A, X_B ⊆ ℝ/ℤ` (here: measurable) with `A = {n > 0 : {nθ} ∈ X_A}`,
`B = {n > 0 : {nθ} ∈ X_B}` and `μ(X_A + X_B) = μ(X_A) + μ(X_B)`, where `μ` is the Haar
probability measure of `ℝ/ℤ` (`volume`; `X_A + X_B` need not be measurable, so `μ` is
used as an outer measure there). -/
def IsCircleRotationPair (A B : Set ℕ) : Prop :=
  ∃ θ : ℝ, 0 < θ ∧ ∃ XA XB : Set Circle1, MeasurableSet XA ∧ MeasurableSet XB ∧
    A = {n | 0 < n ∧ rot θ n ∈ XA} ∧ B = {n | 0 < n ∧ rot θ n ∈ XB} ∧
    volume (XA + XB) = volume XA + volume XB

/-- The question on the problem page, read literally with the circle group:
"are all possible `A` and `B` generated in this way?". It is proved (in a degenerate way,
because nothing prevents `X_A`, `X_B` from being countable null sets) in
`Erdos335.literalCircleQuestion_holds`. -/
def LiteralCircleQuestion : Prop :=
  ∀ A B : Set ℕ, IsErdos335Pair A B → IsCircleRotationPair A B

/-! ### Statement of Ackelsberg–Richter, Theorem 1.4 (stated, **not** proved here) -/

/-- `hℕ = {h, 2h, 3h, …}`. -/
def multiples (h : ℕ) : Set ℕ := {n | 0 < n ∧ h ∣ n}

/-- `B` meets every residue class: `B ∩ (aℕ + b) ≠ ∅` for all `a, b ∈ {1,2,…}`. -/
def MeetsEveryResidueClass (B : Set ℕ) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → ∃ n : ℕ, 0 < n ∧ a * n + b ∈ B

/-- A closed interval (arc) in `𝕋 = ℝ/ℤ`: the image of some `[a, b] ⊆ ℝ`, `a ≤ b`. -/
def IsClosedArc (I : Set Circle1) : Prop :=
  ∃ a b : ℝ, a ≤ b ∧ I = (fun x : ℝ => (x : Circle1)) '' Set.Icc a b

/-- `φ⁻¹(I)` for `φ : hℕ → 𝕋`, `φ(n) = nθ mod 1`. -/
def bohrPreimage (h : ℕ) (θ : ℝ) (I : Set Circle1) : Set ℕ :=
  {n | n ∈ multiples h ∧ rot θ n ∈ I}

/-- `A - t = {n ≥ 1 : n + t ∈ A}`. -/
def shiftDown (A : Set ℕ) (t : ℕ) : Set ℕ := {n | 0 < n ∧ n + t ∈ A}

/-- Theorem 1.4 of Ackelsberg–Richter (arXiv:2604.12864v1), transcribed. It gives the
partial answer to Problem #335 mentioned on the problem page. It is recorded here only as a
statement; it is **not** proved in this project. -/
def AckelsbergRichterTheorem14 : Prop :=
  ∀ (A B : Set ℕ) (dA dB : ℝ) (Ns : ℕ → ℕ),
    A ⊆ Set.Ioi 0 → B ⊆ Set.Ioi 0 → HasDensity A dA → HasDensity B dB →
    0 < dA → dA + dB < 1 → MeetsEveryResidueClass B →
    Tendsto Ns atTop atTop → HasDensityAlong Ns (A + B) (dA + dB) →
    ∃ h : ℕ, 0 < h ∧ ∃ (A0 B0 B1 : Set ℕ) (a0 b0 : ℕ),
      A0 ⊆ multiples h ∧ B0 ⊆ multiples h ∧ a0 < h ∧ b0 < h ∧
      B1 ⊆ Set.Ioi 0 \ multiples h ∧
      A = (fun x => x - a0) '' A0 ∧ B = (fun x => x - b0) '' (B0 ∪ B1) ∧
      ((HasDensity ((Set.Ioi 0 \ multiples h) \ B1) 0 ∧
          ∃ θ : ℝ, Irrational θ ∧ ∃ I J : Set Circle1, IsClosedArc I ∧ IsClosedArc J ∧
            A0 ⊆ bohrPreimage h θ I ∧ B0 ⊆ bohrPreimage h θ J ∧
            HasDensity (bohrPreimage h θ I \ A0) 0 ∧ HasDensity (bohrPreimage h θ J \ B0) 0) ∨
        (HasDensityAlong Ns ((Set.Ioi 0 \ multiples h) \ B1) 0 ∧ HasDensityAlong Ns B0 0 ∧
          ∀ t ∈ multiples h, HasDensityAlong Ns (symmDiff A (shiftDown A t)) 0 ∧
            HasDensityAlong Ns (symmDiff B (shiftDown B t)) 0))


/-!
## The literal circle-rotation formulation is degenerate

The problem page describes pairs of the form `A = {n > 0 : {nθ} ∈ X_A}`,
`B = {n > 0 : {nθ} ∈ X_B}` with `μ(X_A + X_B) = μ(X_A) + μ(X_B)`, and asks whether all
solutions arise "in a similar way". Read literally (no regularity required of `X_A`, `X_B`),
**every** pair of subsets of `{1,2,…}` is of this form: take `θ = √2` and let `X_A`, `X_B` be
the (countable, hence null) sets of points `{nθ}` with `n ∈ A`, resp. `n ∈ B`. Then `X_A + X_B`
is countable too and both sides of the measure equation are `0`.

So a meaningful version of the question needs regularity of `X_A, X_B` (e.g. intervals, as in
the "parallel Bohr intervals" of Ackelsberg–Richter) and/or density-zero modifications.
-/

/-- Membership in a set-builder set (stated locally so the file does not depend on the name
of the corresponding Mathlib simp lemma, which differs between Mathlib versions). -/
@[category API, AMS 11 28]
theorem mem_setBuilder_iff {α : Type*} {p : α → Prop} {a : α} : a ∈ {x | p x} ↔ p a := Iff.rfl

/-- Singletons of `ℝ/ℤ` are Haar-null. -/
@[category API, AMS 11 28]
theorem volume_singleton_circle1 (x : Circle1) : volume ({x} : Set Circle1) = 0 := by
  rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]; simp

/-- Countable subsets of `ℝ/ℤ` are Haar-null. -/
@[category API, AMS 11 28]
theorem volume_countable_circle1 {s : Set Circle1} (hs : s.Countable) : volume s = 0 := by
  rw [← Set.biUnion_of_singleton s, measure_biUnion_null_iff hs]
  exact fun x _ => volume_singleton_circle1 x

/-- For irrational `θ`, `n ↦ {nθ}` is injective on `ℕ`. -/
@[category API, AMS 11 28]
theorem rot_injective {θ : ℝ} (hθ : Irrational θ) : Function.Injective (rot θ) := by
  intro n m hnm
  by_contra hne
  have h0 : ((((n : ℝ) - m) * θ : ℝ) : Circle1) = 0 := by
    have : ((n * θ : ℝ) : Circle1) - ((m * θ : ℝ) : Circle1) = 0 := by
      simpa [rot, sub_eq_zero] using hnm
    rw [← AddCircle.coe_sub] at this
    simpa [sub_mul] using this
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h0
  have hne' : ((n : ℝ) - m) ≠ 0 := by
    intro h; apply hne; exact_mod_cast sub_eq_zero.1 h
  apply hθ
  refine ⟨(k : ℚ) / ((n : ℚ) - m), ?_⟩
  push_cast
  field_simp
  simpa [mul_comm] using hk

/-- **Every** pair `A, B ⊆ {1,2,…}` is a circle-rotation pair in the literal sense of the
problem page (with countable, Haar-null `X_A`, `X_B`). -/
@[category API, AMS 11 28]
theorem isCircleRotationPair_of_pos (A B : Set ℕ) (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) :
    IsCircleRotationPair A B := by
  have hθ : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hinj := rot_injective hθ
  have hpre : ∀ S : Set ℕ, S ⊆ Set.Ioi 0 →
      S = {n | 0 < n ∧ rot (Real.sqrt 2) n ∈ rot (Real.sqrt 2) '' S} := by
    intro S hS
    ext n
    simp only [mem_setBuilder_iff, hinj.mem_set_image]
    exact ⟨fun h => ⟨hS h, h⟩, fun h => h.2⟩
  have hcA : (rot (Real.sqrt 2) '' A).Countable := (Set.to_countable A).image _
  have hcB : (rot (Real.sqrt 2) '' B).Countable := (Set.to_countable B).image _
  have hcAB : (rot (Real.sqrt 2) '' A + rot (Real.sqrt 2) '' B).Countable :=
    hcA.image2 hcB _
  refine ⟨Real.sqrt 2, by positivity, rot (Real.sqrt 2) '' A, rot (Real.sqrt 2) '' B,
    hcA.measurableSet, hcB.measurableSet, hpre A hA, hpre B hB, ?_⟩
  rw [volume_countable_circle1 hcAB, volume_countable_circle1 hcA,
    volume_countable_circle1 hcB, add_zero]

/-- The literal question on the problem page ("are all solutions generated by a circle
rotation with `μ(X_A + X_B) = μ(X_A) + μ(X_B)`?") has a trivially affirmative answer. -/
@[category test, AMS 11 28]
theorem literalCircleQuestion_holds : LiteralCircleQuestion :=
  fun A B h => isCircleRotationPair_of_pos A B h.1 h.2.1


/-!
## Solutions of `d(A + B) = d(A) + d(B)` coming from rotations on finite cyclic groups

For `m ≥ 1` and `X, Y ⊆ ℤ/mℤ`, let `A = {n ≥ 1 : n mod m ∈ X}`, `B = {n ≥ 1 : n mod m ∈ Y}`
(these are the sets "generated" by the rotation `n ↦ n · 1` on the finite group `ℤ/mℤ`).
Then `d(A) = |X|/m`, `d(B) = |Y|/m`, and `A + B` agrees with `{n ≥ 1 : n mod m ∈ X + Y}`
above `m`, so `d(A + B) = |X + Y|/m`. Hence, whenever `X, Y ≠ ∅` and `|X + Y| = |X| + |Y|`,
`(A, B)` is a solution of Erdős Problem #335.
Example: `m = 5`, `X = {0, 1}`, `Y = {0, 2}`, `X + Y = {0, 1, 2, 3}`.
-/

/-- The periodic set `{n ≥ 1 : n mod m ∈ X}`. -/
def periodicSet {m : ℕ} (X : Finset (ZMod m)) : Set ℕ := {n | 0 < n ∧ (n : ZMod m) ∈ X}

@[category API, AMS 11 28]
theorem count_zero (A : Set ℕ) : count A 0 = 0 := by
  classical
  simp [count]

@[category API, AMS 11 28]
theorem count_succ (A : Set ℕ) (N : ℕ) :
    count A (N + 1) = count A N + (by classical exact if N + 1 ∈ A then 1 else 0) := by
  classical
  unfold count
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · convert (add_zero _).symm

/-- A density statement from a uniformly bounded error term. -/
@[category API, AMS 11 28]
theorem tendsto_div_of_bounded (f : ℕ → ℝ) (δ C : ℝ) (h : ∀ N, |f N - δ * N| ≤ C) :
    Tendsto (fun N : ℕ => f N / N) atTop (𝓝 δ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.norm_eq_abs, show f N / N - δ = (f N - δ * N) / N by field_simp, abs_div,
    abs_of_pos hN']
  exact div_le_div_of_nonneg_right (h N) hN'.le

/-- Counting functions of sets agreeing above `K` differ by at most `K`. -/
@[category API, AMS 11 28]
theorem count_le_count_add (A B : Set ℕ) (K : ℕ) (h : ∀ n, K < n → n ∈ A → n ∈ B) (N : ℕ) :
    count A N ≤ count B N + K := by
  classical
  unfold count
  calc ((Finset.Icc 1 N).filter (· ∈ A)).card
      ≤ ((Finset.Icc 1 N).filter (· ∈ B) ∪ Finset.Icc 1 K).card := by
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union] at hn ⊢
        by_cases hK : K < n
        · exact Or.inl ⟨hn.1, h n hK hn.2⟩
        · exact Or.inr ⟨hn.1.1, by omega⟩
    _ ≤ _ := by
        refine (Finset.card_union_le _ _).trans ?_
        simp

/-- If two sets agree above `K` and one has density `δ`, so does the other. -/
@[category API, AMS 11 28]
theorem HasDensity.of_eventually_eq {A B : Set ℕ} {δ : ℝ} (K : ℕ)
    (h : ∀ n, K < n → (n ∈ A ↔ n ∈ B)) (hA : HasDensity A δ) : HasDensity B δ := by
  unfold HasDensity at *
  have hdiff : Tendsto (fun N : ℕ => ((count B N : ℝ) - count A N) / N) atTop (𝓝 0) := by
    have := tendsto_div_of_bounded (fun N => (count B N : ℝ) - count A N) 0 K
      (fun N => by
        have h1 := count_le_count_add A B K (fun n hn => (h n hn).1) N
        have h2 := count_le_count_add B A K (fun n hn => (h n hn).2) N
        rw [zero_mul, sub_zero, abs_le]
        constructor
        · have : (count A N : ℝ) ≤ count B N + K := by exact_mod_cast h1
          linarith
        · have : (count B N : ℝ) ≤ count A N + K := by exact_mod_cast h2
          linarith)
    simpa using this
  have := hA.add hdiff
  rw [add_zero] at this
  refine this.congr fun N => ?_
  rw [← add_div]
  ring_nf

/-- In `[0, m)`, exactly `|X|` integers have residue in `X`. -/
@[category API, AMS 11 28]
theorem nat_count_period {m : ℕ} [NeZero m] (X : Finset (ZMod m)) :
    Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) m = X.card := by
  rw [Nat.count_eq_card_filter_range]
  refine Finset.card_bij (fun n _ => (n : ZMod m)) ?_ ?_ ?_
  · intro n hn
    exact (Finset.mem_filter.1 hn).2
  · intro a ha b hb hab
    have ha' := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
    have hb' := Finset.mem_range.1 (Finset.mem_filter.1 hb).1
    have := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at this
  · intro x hx
    refine ⟨x.val, Finset.mem_filter.2 ⟨Finset.mem_range.2 (ZMod.val_lt x), ?_⟩, ?_⟩
    · simpa using hx
    · simp

@[category API, AMS 11 28]
theorem nat_count_periodic {m : ℕ} [NeZero m] (X : Finset (ZMod m)) (q r : ℕ) :
    Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) (m * q + r) =
      q * X.card + Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show m * (q + 1) + r = m + (m * q + r) by ring, Nat.count_add, nat_count_period]
    have hshift : Nat.count (fun k : ℕ => ((m + k : ℕ) : ZMod m) ∈ X) (m * q + r) =
        Nat.count (fun k : ℕ => (k : ZMod m) ∈ X) (m * q + r) := by
      simp
    rw [hshift, ih]
    ring

@[category API, AMS 11 28]
theorem count_periodicSet_add {m : ℕ} (X : Finset (ZMod m)) (N : ℕ) :
    count (periodicSet X) N + (if ((0 : ℕ) : ZMod m) ∈ X then 1 else 0) =
      Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) (N + 1) := by
  classical
  induction N with
  | zero => simp [count_zero, Nat.count_succ]
  | succ N ih =>
    rw [count_succ, Nat.count_succ, ← ih]
    simp only [periodicSet, mem_setBuilder_iff, Nat.succ_pos, true_and]
    split_ifs <;> omega

/-- An exact quotient-and-remainder expression for the periodic counting function. -/
@[category API, AMS 11 28]
theorem count_periodicSet_div_mod {m : ℕ} [NeZero m] (X : Finset (ZMod m)) (N : ℕ) :
    (count (periodicSet X) N : ℝ) +
      ((if ((0 : ℕ) : ZMod m) ∈ X then 1 else 0 : ℕ) : ℝ) =
      ((N + 1) / m : ℕ) * (X.card : ℝ) +
        (Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) ((N + 1) % m) : ℝ) := by
  have key := count_periodicSet_add X N
  have hc := nat_count_periodic X ((N + 1) / m) ((N + 1) % m)
  rw [Nat.div_add_mod] at hc
  rw [hc] at key
  exact_mod_cast key

/-- `{n ≥ 1 : n mod m ∈ X}` has density `|X| / m`. -/
@[category API, AMS 11 28]
theorem hasDensity_periodicSet {m : ℕ} [NeZero m] (X : Finset (ZMod m)) :
    HasDensity (periodicSet X) (X.card / m) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hXm : (X.card : ℝ) ≤ m := by
    have := Finset.card_le_univ X
    rw [ZMod.card] at this
    exact_mod_cast this
  refine tendsto_div_of_bounded _ _ (m + 2) fun N => ?_
  have key' := count_periodicSet_div_mod X N
  set M := N + 1 with hM
  have hdiv := Nat.div_add_mod M m
  have hr : M % m < m := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))
  have hcr : Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) (M % m) ≤ M % m := Nat.count_le _
  set q := M / m
  set r := M % m
  have hq : (M : ℝ) = m * q + r := by exact_mod_cast hdiv.symm
  have hite : ((if ((0 : ℕ) : ZMod m) ∈ X then 1 else 0 : ℕ) : ℝ) ≤ 1 := by
    split_ifs <;> simp
  have hite0 : (0 : ℝ) ≤ ((if ((0 : ℕ) : ZMod m) ∈ X then 1 else 0 : ℕ) : ℝ) := by positivity
  have hcr' : (Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) r : ℝ) ≤ r := by exact_mod_cast hcr
  have hr' : (r : ℝ) < m := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hN : (N : ℝ) = m * q + r - 1 := by rw [← hq, hM]; push_cast; ring
  have hexp : (X.card : ℝ) / m * N = q * X.card + (r - 1) * X.card / m := by
    rw [hN]; field_simp; ring
  have hX0 : (0 : ℝ) ≤ X.card := by positivity
  have hb1 : ((r : ℝ) - 1) * X.card / m ≤ r := by
    rw [div_le_iff₀ hm]; nlinarith
  have hb2 : -1 ≤ ((r : ℝ) - 1) * X.card / m := by
    rw [le_div_iff₀ hm]; nlinarith
  have hcnt0 : (0 : ℝ) ≤ (Nat.count (fun n : ℕ => (n : ZMod m) ∈ X) r : ℝ) := by positivity
  rw [hexp, abs_le]
  constructor <;> linarith

/-- Above `m`, the sumset of two periodic sets is the periodic set of the sumset. -/
@[category API, AMS 11 28]
theorem mem_periodicSet_add_iff {m : ℕ} [NeZero m] (X Y : Finset (ZMod m)) (n : ℕ)
    (hn : m < n) : n ∈ periodicSet X + periodicSet Y ↔ n ∈ periodicSet (X + Y) := by
  constructor
  · rintro ⟨a, ⟨ha0, ha⟩, b, ⟨hb0, hb⟩, rfl⟩
    refine ⟨by omega, ?_⟩
    push_cast
    exact Finset.add_mem_add ha hb
  · rintro ⟨-, hn'⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.1 hn'
    set b : ℕ := if y.val = 0 then m else y.val with hbdef
    have hb1 : 0 < b := by
      rw [hbdef]; split_ifs with h
      · exact Nat.pos_of_ne_zero (NeZero.ne m)
      · exact Nat.pos_of_ne_zero h
    have hbm : b ≤ m := by
      rw [hbdef]; split_ifs
      · exact le_rfl
      · exact (ZMod.val_lt y).le
    have hby : (b : ZMod m) = y := by
      rw [hbdef]; split_ifs with h
      · rw [ZMod.natCast_self]; exact ((ZMod.val_eq_zero y).1 h).symm
      · simp
    refine ⟨n - b, ⟨by omega, ?_⟩, b, ⟨hb1, by rwa [hby]⟩, by show n - b + b = n; omega⟩
    rw [Nat.cast_sub (by omega), hby, ← hxy]
    simpa using hx

/-- **Rotations on `ℤ/mℤ` give solutions.** If `X, Y ⊆ ℤ/mℤ` are nonempty and
`|X + Y| = |X| + |Y|`, then `A = {n ≥ 1 : n mod m ∈ X}` and `B = {n ≥ 1 : n mod m ∈ Y}`
have positive densities `|X|/m`, `|Y|/m`, and `d(A + B) = d(A) + d(B)`. -/
@[category API, AMS 11 28]
theorem periodicSet_isErdos335Pair {m : ℕ} [NeZero m] (X Y : Finset (ZMod m))
    (hX : X.Nonempty) (hY : Y.Nonempty) (hcard : (X + Y).card = X.card + Y.card) :
    IsErdos335Pair (periodicSet X) (periodicSet Y) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  refine ⟨fun n hn => hn.1, fun n hn => hn.1, X.card / m, Y.card / m,
    div_pos (by exact_mod_cast hX.card_pos) hm, div_pos (by exact_mod_cast hY.card_pos) hm,
    hasDensity_periodicSet X, hasDensity_periodicSet Y, ?_⟩
  have h := hasDensity_periodicSet (X + Y)
  rw [hcard, Nat.cast_add, add_div] at h
  exact h.of_eventually_eq m fun n hn => (mem_periodicSet_add_iff X Y n hn).symm

/-- Concrete instance: `A = {n ≥ 1 : n ≡ 0, 1 (mod 5)}`, `B = {n ≥ 1 : n ≡ 0, 2 (mod 5)}`,
`d(A) = d(B) = 2/5`, `d(A + B) = 4/5`. -/
@[category test, AMS 11 28]
theorem example_mod_five :
    IsErdos335Pair {n | 0 < n ∧ (n % 5 = 0 ∨ n % 5 = 1)} {n | 0 < n ∧ (n % 5 = 0 ∨ n % 5 = 2)} := by
  have hA : {n | 0 < n ∧ (n % 5 = 0 ∨ n % 5 = 1)} = periodicSet ({0, 1} : Finset (ZMod 5)) := by
    ext n
    simp only [periodicSet, mem_setBuilder_iff, Finset.mem_insert, Finset.mem_singleton]
    rw [← ZMod.natCast_mod n 5]
    have : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases (n % 5) <;> simp <;> exact fun _ => by decide
  have hB : {n | 0 < n ∧ (n % 5 = 0 ∨ n % 5 = 2)} = periodicSet ({0, 2} : Finset (ZMod 5)) := by
    ext n
    simp only [periodicSet, mem_setBuilder_iff, Finset.mem_insert, Finset.mem_singleton]
    rw [← ZMod.natCast_mod n 5]
    have : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases (n % 5) <;> simp <;> exact fun _ => by decide
  rw [hA, hB]
  exact periodicSet_isErdos335Pair _ _ (by decide) (by decide) (by decide)


end Erdos335
