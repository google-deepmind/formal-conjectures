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
# Erdős Problem 187

*Reference:* [erdosproblems.com/187](https://www.erdosproblems.com/187)

Originally asked by Cohen. Determine the optimal growth of the length guaranteed
for infinitely many positive common differences in every two-colouring of the integers.
-/



@[expose] public section

namespace Erdos187

open Filter

/-- A $k$-term progression of difference $d$ in the colour class $b$. -/
def HasMonochromaticAP (C : ℤ → Bool) (b : Bool) (d k : ℕ) : Prop :=
  ∃ a : ℤ, ∀ i : ℕ, i < k → C (a + (i : ℤ) * (d : ℤ)) = b

/-- Every two-colouring has one colour class containing progressions of length $f(d)$
for infinitely many positive differences $d$. -/
def IsAdmissible (f : ℕ → ℕ) : Prop :=
  ∀ C : ℤ → Bool, ∃ b : Bool,
    ∃ᶠ d in atTop, 0 < d ∧ HasMonochromaticAP C b d (f d)

set_option linter.style.category_attribute false in
/-- Determine the admissible length functions. The parameter $A$ records an unanswered
set-valued question; this definition does not assert that an answer has been found. -/
@[category research open, AMS 5 11]
def erdos_187 (A : Set (ℕ → ℕ)) : Prop :=
  answer(A) = {f | IsAdmissible f}

/-- Infinitely many natural-number differences means an infinite set of differences. -/
@[category API, AMS 5 11]
theorem isAdmissible_iff_infinite (f : ℕ → ℕ) :
    IsAdmissible f ↔ ∀ C : ℤ → Bool, ∃ b : Bool,
      {d : ℕ | 0 < d ∧ HasMonochromaticAP C b d (f d)}.Infinite := by
  simp only [IsAdmissible, Nat.frequently_atTop_iff_infinite]

/-- Allowing the colour to depend on $d$ gives the same admissibility condition. -/
@[category API, AMS 5 11]
theorem isAdmissible_iff_frequently (f : ℕ → ℕ) :
    IsAdmissible f ↔ ∀ C : ℤ → Bool,
      ∃ᶠ d in atTop, ∃ b : Bool, 0 < d ∧ HasMonochromaticAP C b d (f d) := by
  simp only [IsAdmissible, frequently_exists]

/-- Shortening a monochromatic progression preserves its colour and difference. -/
@[category API, AMS 5 11]
theorem HasMonochromaticAP.mono {C : ℤ → Bool} {b : Bool} {d k l : ℕ}
    (h : HasMonochromaticAP C b d l) (hkl : k ≤ l) : HasMonochromaticAP C b d k := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun i hi => ha i (lt_of_lt_of_le hi hkl)⟩

/-- The $k$ terms are distinct when the common difference is positive. -/
@[category API, AMS 5 11]
theorem progression_card (a : ℤ) {d : ℕ} (hd : 0 < d) (k : ℕ) :
    ((Finset.range k).image (fun i : ℕ => a + (i : ℤ) * (d : ℤ))).card = k := by
  have hinj : Function.Injective (fun i : ℕ => a + (i : ℤ) * (d : ℤ)) := by
    intro i j hij
    have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    have h : (i : ℤ) = (j : ℤ) := mul_right_cancel₀ hd' (add_left_cancel hij)
    exact_mod_cast h
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- Admissibility is closed under pointwise shortening. -/
@[category API, AMS 5 11]
theorem IsAdmissible.mono {f g : ℕ → ℕ} (hg : IsAdmissible g)
    (hfg : ∀ d, f d ≤ g d) : IsAdmissible f := by
  intro C
  obtain ⟨b, hb⟩ := hg C
  exact ⟨b, hb.mono fun d hd => ⟨hd.1, hd.2.mono (hfg d)⟩⟩

/-- Changing finitely many values of a length function does not affect admissibility. -/
@[category API, AMS 5 11]
theorem isAdmissible_congr {f g : ℕ → ℕ} (hfg : f =ᶠ[atTop] g) :
    IsAdmissible f ↔ IsAdmissible g := by
  unfold IsAdmissible
  apply forall_congr'
  intro C
  apply exists_congr
  intro b
  exact frequently_congr (hfg.mono fun d hd => by rw [hd])

/-- Van der Waerden's theorem gives a progression of every fixed length whose
positive common difference exceeds any prescribed bound. -/
@[category research solved, AMS 5 11]
theorem monochromaticAP_above (C : ℤ → Bool) (k N : ℕ) :
    ∃ d > N, ∃ b : Bool, HasMonochromaticAP C b d k := by
  obtain ⟨t, ht, a, b, h⟩ := Combinatorics.exists_mono_homothetic_copy
    (Finset.range k) (fun n : ℕ => C (((N + 1) * n : ℕ) : ℤ))
  refine ⟨t * (N + 1), by nlinarith, b, (((N + 1) * a : ℕ) : ℤ), ?_⟩
  intro i hi
  convert h i (Finset.mem_range.mpr hi) using 1
  simp only [nsmul_eq_mul, Nat.cast_id, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  congr 1
  ring

/-- Every constant length function is admissible, by van der Waerden's theorem. -/
@[category research solved, AMS 5 11]
theorem constant_isAdmissible (k : ℕ) : IsAdmissible (fun _ => k) := by
  rw [isAdmissible_iff_frequently]
  intro C
  apply frequently_atTop.mpr
  intro N
  obtain ⟨d, hd, b, hb⟩ := monochromaticAP_above C k N
  exact ⟨d, hd.le, b, lt_of_le_of_lt (Nat.zero_le N) hd, hb⟩

/-- A function eventually bounded by a fixed constant is admissible. -/
@[category API, AMS 5 11]
theorem isAdmissible_of_eventually_bounded {f : ℕ → ℕ} {k : ℕ}
    (hf : ∀ᶠ d in atTop, f d ≤ k) : IsAdmissible f := by
  intro C
  obtain ⟨b, hb⟩ := constant_isAdmissible k C
  exact ⟨b, (hb.and_eventually hf).mono fun d hd =>
    ⟨hd.1.1, hd.1.2.mono hd.2⟩⟩

/-- Admissibility is preserved when a single value of the length function is changed. -/
@[category API, AMS 5 11]
theorem IsAdmissible.update {f : ℕ → ℕ} (hf : IsAdmissible f) (d₀ k : ℕ) :
    IsAdmissible (Function.update f d₀ k) := by
  have hfg : f =ᶠ[atTop] Function.update f d₀ k := by
    filter_upwards [eventually_gt_atTop d₀] with d hd
    simp [Function.update_of_ne (ne_of_gt hd)]
  exact (isAdmissible_congr hfg).mp hf

/-- There is no pointwise greatest admissible function, even if comparisons are
restricted to positive differences. A single positive value can always be increased. -/
@[category API, AMS 5 11]
theorem no_greatest_admissible : ¬ ∃ f : ℕ → ℕ,
    IsAdmissible f ∧ ∀ g : ℕ → ℕ, IsAdmissible g → ∀ d > 0, g d ≤ f d := by
  rintro ⟨f, hf, hmax⟩
  have h := hmax (Function.update f 1 (f 1 + 1)) (hf.update 1 (f 1 + 1)) 1 (by omega)
  simp at h

/-- A uniform bound on the difference for progressions of a fixed length. -/
@[category research solved, AMS 5 11]
theorem exists_uniform_difference_bound (k : ℕ) :
    ∃ D : ℕ, ∀ C : ℤ → Bool,
      ∃ d : ℕ, 0 < d ∧ d ≤ D ∧ ∃ b : Bool, HasMonochromaticAP C b d k := by
  classical
  obtain ⟨ι, inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin (k + 1)) Bool
  let := inst
  refine ⟨Fintype.card ι, ?_⟩
  intro C
  obtain ⟨l, b, hl⟩ := hι (fun v => C (∑ j, ((v j).val : ℤ)))
  let s : Finset ι := Finset.univ.filter (fun j => l.idxFun j = none)
  let a : ℤ := ∑ j ∈ sᶜ, ((l.idxFun j).map (fun x => (x.val : ℤ))).getD 0
  have heq (i : Fin (k + 1)) : (∑ j, ((l i j).val : ℤ)) = (s.card : ℤ) * i.val + a := by
    rw [← Finset.sum_add_sum_compl s]
    congr 1
    · rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : l.idxFun j = none := (Finset.mem_filter.mp hj).2
      rw [l.apply_none _ _ hj']
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' : l.idxFun j ≠ none := by simpa [s] using hj
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp hj'
      simp [← hx]
  have hs : 0 < s.card := Finset.card_pos.mpr
    ⟨l.proper.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, l.proper.choose_spec⟩⟩
  refine ⟨s.card, hs, Finset.card_le_univ s, b, a, ?_⟩
  intro i hi
  have h := hl ⟨i, by omega⟩
  simpa only [heq, add_comm, mul_comm] using h

/-- Increasing thresholds adapted to uniform difference bounds. -/
def threshold (B : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => threshold B n * (B n + 1) + 1

@[category API, AMS 5 11]
theorem threshold_strictMono (B : ℕ → ℕ) : StrictMono (threshold B) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [threshold]
  have h : threshold B n ≤ threshold B n * (B n + 1) := by nlinarith
  omega

@[category API, AMS 5 11]
theorem lt_threshold (B : ℕ → ℕ) (n : ℕ) : n < threshold B n := by
  induction n with
  | zero => simp [threshold]
  | succ n ih =>
    have h := threshold_strictMono B (Nat.lt_succ_self n)
    simp only [Nat.succ_eq_add_one] at h
    change n + 1 < threshold B (n + 1)
    omega

/-- A slow length function, obtained by inverting the thresholds. -/
noncomputable def slowLength (B : ℕ → ℕ) (d : ℕ) : ℕ :=
  Nat.find (show ∃ k, d < threshold B (k + 1) from
    ⟨d, lt_trans (Nat.lt_succ_self d) (lt_threshold B (d + 1))⟩)

@[category API, AMS 5 11]
theorem slowLength_le {B : ℕ → ℕ} {d k : ℕ} (h : d < threshold B (k + 1)) :
    slowLength B d ≤ k := by
  exact Nat.find_min' _ h

@[category API, AMS 5 11]
theorem slowLength_tendsto (B : ℕ → ℕ) : Tendsto (slowLength B) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (threshold B (k + 1))] with d hd
  have hspec : d < threshold B (slowLength B d + 1) := by
    unfold slowLength
    exact Nat.find_spec (p := fun k => d < threshold B (k + 1)) _
  have hk : k + 1 < slowLength B d + 1 := by
    apply (threshold_strictMono B).lt_iff_lt.mp
    exact lt_of_le_of_lt hd hspec
  omega

/-- The threshold inverse is monotone. -/
@[category API, AMS 5 11]
theorem slowLength_monotone (B : ℕ → ℕ) : Monotone (slowLength B) := by
  intro d e hde
  apply slowLength_le
  have he : e < threshold B (slowLength B e + 1) := by
    unfold slowLength
    exact Nat.find_spec (p := fun k => e < threshold B (k + 1)) _
  exact lt_of_le_of_lt hde he

/-- Scaling a colouring scales the common difference of a progression. -/
@[category API, AMS 5 11]
theorem HasMonochromaticAP.scale {C : ℤ → Bool} {b : Bool} {d k n : ℕ}
    (h : HasMonochromaticAP (fun z => C ((n : ℤ) * z)) b d k) :
    HasMonochromaticAP C b (n * d) k := by
  obtain ⟨a, ha⟩ := h
  refine ⟨(n : ℤ) * a, ?_⟩
  intro i hi
  convert ha i hi using 1
  congr 1
  push_cast
  ring

/-- Van der Waerden's theorem supplies a single admissible length function tending
to infinity. It does not determine the optimal rate of growth. -/
@[category research solved, AMS 5 11]
theorem exists_admissible_tendsto : ∃ f : ℕ → ℕ,
    IsAdmissible f ∧ Tendsto f atTop atTop := by
  classical
  choose B hB using exists_uniform_difference_bound
  refine ⟨slowLength B, ?_, slowLength_tendsto B⟩
  rw [isAdmissible_iff_frequently]
  intro C
  apply frequently_atTop.mpr
  intro N
  let n := threshold B N
  obtain ⟨e, he, heB, b, hb⟩ := hB N (fun z => C ((n : ℤ) * z))
  have hn : N < n := lt_threshold B N
  have hne : n ≤ n * e := by nlinarith
  have hd : n * e < threshold B (N + 1) := by
    rw [threshold]
    dsimp [n] at *
    nlinarith
  refine ⟨n * e, by omega, b, by nlinarith, ?_⟩
  exact hb.scale.mono (slowLength_le hd)

end Erdos187
