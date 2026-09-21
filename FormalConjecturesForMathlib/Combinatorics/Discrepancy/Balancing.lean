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

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

/-!
# Balancing vectors with nearly translation-invariant distributions

This file proves the combinatorial half of the elementary proof of the Komlós conjecture
by Karingula and Lovett. Let $P$ be a finitely supported probability distribution on a real
vector space $E$, with mean $\mu(P)$. Its *overlap* with its translate by $u$ is
$$\sum_x \min\{P(x), P(x - u)\} = 1 - d_{\mathrm{TV}}(P, P + u).$$
The main result `Finsupp.exists_signs_mean_add_sum_eq_mean` states: if the overlap of $P$ with
its translate by $6 v_i$ is at least $2/3$ for $i = 1, \dots, n$, then there are signs
$\varepsilon_i \in \{-1, 1\}$ and a probability distribution $R$ supported inside the support
of $P$ whose mean is $\mu(P) + \sum_i \varepsilon_i v_i$.

The proof is by induction on $n$, simultaneously over all spaces $E$. The inductive step
uses the *splitting operator* `Finsupp.bitSplit`, which sends a distribution on $E$ to a
distribution on $E × ℝ$ whose last coordinate is a bit recording how much mass has two
available parents.

## References

* [S. R. Karingula and S. Lovett, *An elementary proof of the Komlós conjecture*,
  arXiv:2609.20979](https://arxiv.org/abs/2609.20979), Section 3.
-/

@[expose] public section

open Finset

namespace Finsupp

section Mass

variable {E : Type*}

/-- The total mass of a finitely supported function `P : E →₀ ℝ`. -/
def mass (P : E →₀ ℝ) : ℝ := P.sum fun _ p => p

/-- A finitely supported function `P : E →₀ ℝ` is a probability distribution if it is nonnegative
and has total mass `1`. -/
structure IsProbDist (P : E →₀ ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ P x
  mass_eq_one : mass P = 1

theorem mass_add (P Q : E →₀ ℝ) : mass (P + Q) = mass P + mass Q :=
  sum_add_index' (fun _ => rfl) fun _ _ _ => rfl

theorem mass_smul (c : ℝ) (P : E →₀ ℝ) : mass (c • P) = c * mass P := by
  rw [mass, mass, sum_smul_index' (h := fun _ p => p) (fun _ => rfl), Finsupp.mul_sum]
  rfl

theorem mass_mapDomain {F : Type*} (f : E → F) (P : E →₀ ℝ) : mass (mapDomain f P) = mass P :=
  sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl

theorem mass_nonneg {P : E →₀ ℝ} (hP : ∀ x, 0 ≤ P x) : 0 ≤ mass P :=
  Finset.sum_nonneg fun x _ => hP x

theorem mapDomain_apply_nonneg {F : Type*} (f : E → F) {P : E →₀ ℝ} (hP : ∀ x, 0 ≤ P x) (y : F) :
    0 ≤ mapDomain f P y := by
  classical
  simp only [mapDomain, sum_apply, single_apply]
  exact Finset.sum_nonneg fun x _ => by dsimp only; split_ifs <;> simp [hP x]

/-- Sums of `g x (P x)` may be taken over any finset containing the support of `P`, provided
`g x 0 = 0`. -/
theorem sum_eq_sum_of_ne_zero_mem {P : E →₀ ℝ} {s : Finset E} (hs : ∀ x, P x ≠ 0 → x ∈ s)
    {M : Type*} [AddCommMonoid M] (g : E → ℝ → M) (hg : ∀ x, g x 0 = 0) :
    P.sum g = ∑ x ∈ s, g x (P x) :=
  sum_of_support_subset P (fun x hx => hs x (mem_support_iff.1 hx)) g fun x _ => hg x

end Mass

section Group

variable {E : Type*} [AddCommGroup E]

/-- Reindexing a sum along a translation. -/
theorem sum_translate (P : E →₀ ℝ) {A : Finset E} (u : E) (hA : ∀ x, P (x + u) ≠ 0 → x ∈ A)
    {M : Type*} [AddCommMonoid M] (g : E → ℝ → M) (hg : ∀ x, g x 0 = 0) :
    ∑ x ∈ A, g x (P (x + u)) = P.sum fun y p => g (y - u) p := by
  classical
  rw [sum_eq_sum_of_ne_zero_mem (s := A.image (· + u)) (fun y hy => ?_) _ (fun x => hg _),
    Finset.sum_image (fun x _ y _ h => add_right_cancel h)]
  · simp
  · exact mem_image.2 ⟨y - u, hA _ (by simpa using hy), sub_add_cancel y u⟩

end Group

section Mean

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The mean of a finitely supported function `P : E →₀ ℝ`, that is, `∑ x, P x • x`. -/
def mean (P : E →₀ ℝ) : E := P.sum fun x p => p • x

/-- The overlap `∑ x, min (P x) (P (x - u))` of `P` with its translate by `u`. For a probability
distribution `P`, this is `1 - d_TV(P, P + u)`. -/
def overlap (P : E →₀ ℝ) (u : E) : ℝ := P.sum fun x p => min p (P (x - u))

theorem mean_add (P Q : E →₀ ℝ) : mean (P + Q) = mean P + mean Q :=
  sum_add_index' (fun _ => zero_smul ℝ _) fun _ _ _ => add_smul _ _ _

theorem mean_smul (c : ℝ) (P : E →₀ ℝ) : mean (c • P) = c • mean P := by
  rw [mean, mean, sum_smul_index' (h := fun x p => p • x) (fun _ => zero_smul ℝ _), Finsupp.sum,
    Finsupp.sum, Finset.smul_sum]
  simp only [smul_eq_mul, mul_smul]

omit [AddCommGroup E] [Module ℝ E] in
/-- The mean of the pushforward of `P` along `fun x => f x + c`. -/
theorem mean_mapDomain_add_const {F : Type*} [AddCommGroup F] [Module ℝ F] (f : E → F) (c : F)
    (P : E →₀ ℝ) :
    mean (mapDomain (fun x => f x + c) P) = P.sum (fun x p => p • f x) + mass P • c := by
  rw [mean, sum_mapDomain_index (h := fun y p => p • y) (fun _ => zero_smul ℝ _)
    fun _ _ _ => add_smul _ _ _]
  simp only [Finsupp.sum, mass, smul_add, Finset.sum_add_distrib, Finset.sum_smul]

omit [AddCommGroup E] [Module ℝ E] in
/-- The mean of the pushforward of `P` along `fun x => f x - c`. -/
theorem mean_mapDomain_sub_const {F : Type*} [AddCommGroup F] [Module ℝ F] (f : E → F) (c : F)
    (P : E →₀ ℝ) :
    mean (mapDomain (fun x => f x - c) P) = P.sum (fun x p => p • f x) - mass P • c := by
  simp only [sub_eq_add_neg, mean_mapDomain_add_const, smul_neg]

theorem mean_fst {F : Type*} [AddCommGroup F] [Module ℝ F] (P : E × F →₀ ℝ) :
    (mean P).1 = P.sum fun y p => p • y.1 := by
  simp [mean, Finsupp.sum, Prod.fst_sum]

theorem mean_snd {F : Type*} [AddCommGroup F] [Module ℝ F] (P : E × F →₀ ℝ) :
    (mean P).2 = P.sum fun y p => p • y.2 := by
  simp [mean, Finsupp.sum, Prod.snd_sum]

/-- The mean of a probability distribution supported in a box `{x | ∀ j, |x j| ≤ c}`
lies in that box. -/
theorem abs_mean_apply_le {ι : Type*} {P : (ι → ℝ) →₀ ℝ} (hP : IsProbDist P) {c : ℝ}
    (hsupp : ∀ x, P x ≠ 0 → ∀ j, |x j| ≤ c) (j : ι) : |mean P j| ≤ c := by
  have hc : 0 ≤ c := by
    obtain ⟨x, hx⟩ : ∃ x, P x ≠ 0 := by
      by_contra! h
      have := hP.mass_eq_one
      simp [mass, Finsupp.sum, h] at this
    exact (abs_nonneg _).trans (hsupp x hx j)
  calc |mean P j| = |∑ x ∈ P.support, P x * x j| := by simp [mean, Finsupp.sum, Finset.sum_apply]
    _ ≤ ∑ x ∈ P.support, |P x * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ P.support, P x * c := by
      refine Finset.sum_le_sum fun x hx => ?_
      rw [abs_mul, abs_of_nonneg (hP.nonneg x)]
      exact mul_le_mul_of_nonneg_left (hsupp x (mem_support_iff.1 hx) j) (hP.nonneg x)
    _ = c := by
      have hm : ∑ x ∈ P.support, P x = 1 := hP.mass_eq_one
      rw [← Finset.sum_mul, hm, one_mul]

end Mean

section BitSplit

variable {E : Type*} [AddCommGroup E]

/-- The translate of `P` by `u`, so that `translate u P x = P (x - u)`. -/
noncomputable def translate (u : E) (P : E →₀ ℝ) : E →₀ ℝ := mapDomain (· + u) P

@[simp]
theorem translate_apply (u : E) (P : E →₀ ℝ) (x : E) : translate u P x = P (x - u) := by
  conv_lhs => rw [← sub_add_cancel x u]
  exact mapDomain_apply (add_left_injective u) P (x - u)

open scoped Classical in
/-- The splitting operator: a state `(x, b)` of `bitSplit v P` has parents `x + v` and `x - v`
in `P`. The state with bit `0` receives half of the larger parent mass and the state with bit `1`
receives half of the smaller parent mass. -/
noncomputable def bitSplit (v : E) (P : E →₀ ℝ) : E × ℝ →₀ ℝ :=
  onFinset ((P.support.image (· - v) ∪ P.support.image (· + v)) ×ˢ {0, 1})
    (fun y => if y.2 = 0 then max (P (y.1 + v)) (P (y.1 - v)) / 2
      else if y.2 = 1 then min (P (y.1 + v)) (P (y.1 - v)) / 2 else 0)
    (by
      rintro ⟨x, b⟩ h
      have key : P (x + v) ≠ 0 ∨ P (x - v) ≠ 0 := by
        by_contra! h'
        simp [h'.1, h'.2] at h
      simp only [mem_product, mem_union, mem_image, mem_support_iff, mem_insert, mem_singleton]
      refine ⟨?_, ?_⟩
      · rcases key with h1 | h1
        · exact Or.inl ⟨x + v, h1, add_sub_cancel_right x v⟩
        · exact Or.inr ⟨x - v, h1, sub_add_cancel x v⟩
      · by_contra! hb
        simp [hb.1, hb.2] at h)

theorem bitSplit_apply (v : E) (P : E →₀ ℝ) (y : E × ℝ) :
    bitSplit v P y = if y.2 = 0 then max (P (y.1 + v)) (P (y.1 - v)) / 2
      else if y.2 = 1 then min (P (y.1 + v)) (P (y.1 - v)) / 2 else 0 := rfl

@[simp]
theorem bitSplit_apply_zero (v : E) (P : E →₀ ℝ) (x : E) :
    bitSplit v P (x, 0) = max (P (x + v)) (P (x - v)) / 2 := by
  simp [bitSplit_apply]

@[simp]
theorem bitSplit_apply_one (v : E) (P : E →₀ ℝ) (x : E) :
    bitSplit v P (x, 1) = min (P (x + v)) (P (x - v)) / 2 := by
  simp [bitSplit_apply]

theorem bitSplit_apply_of_ne (v : E) (P : E →₀ ℝ) {x : E} {b : ℝ} (hb : b ≠ 0) (hb' : b ≠ 1) :
    bitSplit v P (x, b) = 0 := by
  simp [bitSplit_apply, hb, hb']

theorem snd_eq_zero_or_one_of_bitSplit_ne_zero (v : E) (P : E →₀ ℝ) {y : E × ℝ}
    (hy : bitSplit v P y ≠ 0) : y.2 = 0 ∨ y.2 = 1 := by
  by_contra! h
  exact hy (bitSplit_apply_of_ne v P h.1 h.2)

theorem ne_zero_or_ne_zero_of_bitSplit_apply_zero_ne_zero (v : E) (P : E →₀ ℝ) {x : E}
    (hx : bitSplit v P (x, 0) ≠ 0) : P (x + v) ≠ 0 ∨ P (x - v) ≠ 0 := by
  by_contra! h
  simp [h.1, h.2] at hx

theorem ne_zero_and_ne_zero_of_bitSplit_apply_one_ne_zero (v : E) {P : E →₀ ℝ} (hP : ∀ x, 0 ≤ P x)
    {x : E} (hx : bitSplit v P (x, 1) ≠ 0) : P (x + v) ≠ 0 ∧ P (x - v) ≠ 0 := by
  refine ⟨fun h => hx ?_, fun h => hx ?_⟩
  · simp [h, min_eq_left (hP (x - v))]
  · simp [h, min_eq_right (hP (x + v))]

theorem bitSplit_nonneg (v : E) {P : E →₀ ℝ} (hP : ∀ x, 0 ≤ P x) (y : E × ℝ) :
    0 ≤ bitSplit v P y := by
  rw [bitSplit_apply]
  split_ifs
  · exact div_nonneg (le_max_of_le_left (hP _)) two_pos.le
  · exact div_nonneg (le_min (hP _) (hP _)) two_pos.le
  · exact le_rfl

theorem bitSplit_mono (v : E) {P Q : E →₀ ℝ} (h : ∀ x, P x ≤ Q x) (y : E × ℝ) :
    bitSplit v P y ≤ bitSplit v Q y := by
  rw [bitSplit_apply, bitSplit_apply]
  split_ifs
  · exact div_le_div_of_nonneg_right (max_le_max (h _) (h _)) two_pos.le
  · exact div_le_div_of_nonneg_right (min_le_min (h _) (h _)) two_pos.le
  · exact le_rfl

theorem bitSplit_translate_apply (v u : E) (P : E →₀ ℝ) (y : E × ℝ) :
    bitSplit v (translate u P) y = bitSplit v P (y - (u, 0)) := by
  obtain ⟨x, b⟩ := y
  have h1 : x - u + v = x + v - u := by abel
  have h2 : x - u - v = x - v - u := by abel
  simp only [bitSplit_apply, translate_apply, Prod.mk_sub_mk, sub_zero, h1, h2]

theorem bitSplit_ne_zero_mem (v : E) (P : E →₀ ℝ) {y : E × ℝ} (hy : bitSplit v P y ≠ 0) :
    haveI := Classical.decEq E
    y ∈ (P.support.image (· - v) ∪ P.support.image (· + v)) ×ˢ ({0, 1} : Finset ℝ) :=
  support_onFinset_subset (mem_support_iff.2 hy)

/-- Summing `bitSplit v P` against a function of the first coordinate. -/
theorem sum_bitSplit_fst (v : E) (P : E →₀ ℝ) {M : Type*} [AddCommGroup M] [Module ℝ M]
    (g : E → M) :
    (bitSplit v P).sum (fun y p => p • g y.1) =
      (1 / 2 : ℝ) • (P.sum fun x p => p • g (x - v)) +
        (1 / 2 : ℝ) • (P.sum fun x p => p • g (x + v)) := by
  classical
  set A := P.support.image (· - v) ∪ P.support.image (· + v) with hA
  rw [sum_eq_sum_of_ne_zero_mem (s := A ×ˢ ({0, 1} : Finset ℝ))
    (fun y hy => by simpa [A] using bitSplit_ne_zero_mem v P hy) (fun y p => p • g y.1)
    (fun _ => zero_smul ℝ _), Finset.sum_product]
  simp only [Finset.sum_pair (zero_ne_one' ℝ), bitSplit_apply_zero, bitSplit_apply_one]
  have h1 : ∑ x ∈ A, P (x + v) • g x = P.sum fun y p => p • g (y - v) :=
    sum_translate P v (fun x hx => by
      simp only [A, mem_union, mem_image, mem_support_iff]
      exact Or.inl ⟨x + v, hx, add_sub_cancel_right x v⟩)
      (fun x p => p • g x) (fun _ => zero_smul ℝ _)
  have h2 : ∑ x ∈ A, P (x - v) • g x = P.sum fun y p => p • g (y + v) := by
    have := sum_translate P (A := A) (-v) (fun x hx => by
      simp only [A, mem_union, mem_image, mem_support_iff]
      exact Or.inr ⟨x + -v, hx, by abel⟩)
      (fun x p => p • g x) (fun _ => zero_smul ℝ _)
    simpa only [← sub_eq_add_neg, sub_neg_eq_add] using this
  rw [← h1, ← h2, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← add_smul, ← add_div, max_add_min]
  module

theorem mass_bitSplit (v : E) (P : E →₀ ℝ) : mass (bitSplit v P) = mass P := by
  have := sum_bitSplit_fst v P (M := ℝ) fun _ => 1
  simp only [smul_eq_mul, mul_one] at this
  rw [mass, mass, this]
  ring

/-- Splitting does not decrease the overlap with translates (the shift distance does not
increase). -/
theorem overlap_le_overlap_bitSplit (v u : E) {P : E →₀ ℝ} (hP : ∀ x, 0 ≤ P x) :
    overlap P u ≤ overlap (bitSplit v P) (u, 0) := by
  set H : E →₀ ℝ := onFinset P.support (fun x => min (P x) (P (x - u))) (by
    intro x hx
    rw [mem_support_iff]
    contrapose! hx
    simp [hx, min_eq_left (hP (x - u))]) with hH
  have hH0 : ∀ x, 0 ≤ H x := fun x => le_min (hP x) (hP (x - u))
  have hH1 : ∀ x, H x ≤ P x := fun x => min_le_left _ _
  have hH2 : ∀ x, H x ≤ translate u P x := fun x => by
    rw [translate_apply]; exact min_le_right (P x) (P (x - u))
  have hHP : overlap P u = mass H := by
    rw [overlap, mass, sum_eq_sum_of_ne_zero_mem (P := H) (s := P.support)
      (fun x hx => support_onFinset_subset (mem_support_iff.2 hx)) _ (fun _ => rfl)]
    rfl
  have hle : ∀ y, bitSplit v H y ≤ min (bitSplit v P y) (bitSplit v P (y - (u, 0))) := fun y =>
    le_min (bitSplit_mono v hH1 y) (by rw [← bitSplit_translate_apply]; exact bitSplit_mono v hH2 y)
  calc overlap P u = mass H := hHP
    _ = mass (bitSplit v H) := (mass_bitSplit v H).symm
    _ = ∑ y ∈ (bitSplit v P).support, bitSplit v H y := by
      rw [mass, sum_eq_sum_of_ne_zero_mem (s := (bitSplit v P).support) _ _ (fun _ => rfl)]
      intro y hy
      rw [mem_support_iff]
      intro h
      exact hy (le_antisymm ((hle y).trans (by rw [h]; exact min_le_left _ _))
        (bitSplit_nonneg v hH0 y))
    _ ≤ ∑ y ∈ (bitSplit v P).support, min (bitSplit v P y) (bitSplit v P (y - (u, 0))) :=
      Finset.sum_le_sum fun y _ => hle y
    _ = overlap (bitSplit v P) (u, 0) := rfl

section Module

variable [Module ℝ E]

theorem mean_bitSplit_fst (v : E) {P : E →₀ ℝ} (hP : mass P = 1) :
    (mean (bitSplit v P)).1 = mean P := by
  rw [mean_fst, sum_bitSplit_fst v P fun x => x]
  have hm : ∑ x ∈ P.support, P x = 1 := hP
  simp only [Finsupp.sum, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_smul, hm, one_smul, mean]
  module

theorem mean_bitSplit_snd (v : E) {P : E →₀ ℝ} (hP : ∀ x, 0 ≤ P x) :
    (mean (bitSplit v P)).2 = overlap P ((2 : ℝ) • v) / 2 := by
  classical
  set A := P.support.image (· - v) ∪ P.support.image (· + v) with hA
  rw [mean_snd, sum_eq_sum_of_ne_zero_mem (s := A ×ˢ ({0, 1} : Finset ℝ))
    (fun y hy => by simpa [A] using bitSplit_ne_zero_mem v P hy) (fun y p => p • y.2)
    (fun _ => zero_smul ℝ _), Finset.sum_product]
  simp only [Finset.sum_pair (zero_ne_one' ℝ), bitSplit_apply_zero, bitSplit_apply_one, smul_eq_mul,
    mul_zero, mul_one, zero_add, ← Finset.sum_div]
  congr 1
  have h : ∑ x ∈ A, min (P (x + v)) (P (x - v)) = P.sum fun y p => min p (P (y - v - v)) :=
    sum_translate P v (fun x hx => by
      simp only [A, mem_union, mem_image, mem_support_iff]
      exact Or.inl ⟨x + v, hx, add_sub_cancel_right x v⟩)
      (fun x p => min p (P (x - v))) (fun x => min_eq_left (hP (x - v)))
  rw [h, overlap]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [sub_sub, ← two_smul ℝ v]

end Module

end BitSplit

section Balancing

universe u

/-- **The balancing lemma** (Karingula–Lovett, Lemma 1.3). Let `P` be a finitely supported
probability distribution on a real vector space whose overlap with each of its translates by
`6 • v i` is at least `2 / 3`. Then there are signs `ε i ∈ {-1, 1}` and a probability
distribution `R` supported inside the support of `P` with mean `P.mean + ∑ i, ε i • v i`.
In particular `P.mean + ∑ i, ε i • v i` lies in the convex hull of the support of `P`. -/
theorem exists_signs_isProbDist_mean_eq (n : ℕ) :
    ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (v : Fin n → E) (P : E →₀ ℝ),
      P.IsProbDist → (∀ i, 2 / 3 ≤ P.overlap ((6 : ℝ) • v i)) →
      ∃ ε : Fin n → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∃ R : E →₀ ℝ, R.IsProbDist ∧
        (∀ x, R x ≠ 0 → P x ≠ 0) ∧ R.mean = P.mean + ∑ i, ε i • v i := by
  induction n with
  | zero =>
    intro E _ _ v P hP _
    exact ⟨Fin.elim0, fun i => i.elim0, P, hP, fun _ h => h, by simp⟩
  | succ n ih =>
    intro E _ _ v P hP hov
    classical
    set w := v (Fin.last n) with hw
    set Q := bitSplit ((3 : ℝ) • w) P with hQ
    have hQprob : Q.IsProbDist :=
      ⟨bitSplit_nonneg _ hP.nonneg, by rw [hQ, mass_bitSplit, hP.mass_eq_one]⟩
    set β := P.overlap ((6 : ℝ) • w) / 2 with hβ
    have hβ3 : 1 / 3 ≤ β := by
      have := hov (Fin.last n)
      rw [hβ]
      linarith
    have hQ1 : (mean Q).1 = mean P := mean_bitSplit_fst _ hP.mass_eq_one
    have hQ2 : (mean Q).2 = β := by
      rw [hQ, mean_bitSplit_snd _ hP.nonneg, hβ, smul_smul]
      norm_num
    obtain ⟨ε', hε', R, hR, hRQ, hRmean⟩ :=
      ih (fun i => (v i.castSucc, (0 : ℝ))) Q hQprob fun i => by
        rw [Prod.smul_mk, smul_zero]
        exact (hov i.castSucc).trans (overlap_le_overlap_bitSplit _ _ hP.nonneg)
    have hR1 : (mean R).1 = mean P + ∑ i, ε' i • v i.castSucc := by
      rw [hRmean, Prod.fst_add, hQ1, Prod.fst_sum]
      simp
    have hR2 : (mean R).2 = β := by
      rw [hRmean, Prod.snd_add, hQ2, Prod.snd_sum]
      simp
    have hRsnd : ∀ y, R y ≠ 0 → y.2 = 0 ∨ y.2 = 1 := fun y hy =>
      snd_eq_zero_or_one_of_bitSplit_ne_zero _ _ (hRQ y hy)
    -- Split `R` into the states with bit `0` whose parent `x + 3 v` is available, the remaining
    -- states with bit `0`, and the states with bit `1`.
    set Rp := R.filter (fun y => y.2 = 0 ∧ P (y.1 + (3 : ℝ) • w) ≠ 0) with hRp
    set Rm := R.filter (fun y => y.2 = 0 ∧ P (y.1 + (3 : ℝ) • w) = 0) with hRm
    set R₁ := R.filter (fun y => y.2 ≠ 0) with hR₁
    have hdecomp : R = Rp + Rm + R₁ := by
      ext y
      simp only [hRp, hRm, hR₁, coe_add, Pi.add_apply, filter_apply]
      by_cases h1 : y.2 = 0 <;> by_cases h2 : P (y.1 + (3 : ℝ) • w) = 0 <;> simp [h1, h2]
    have hnn : ∀ (p : E × ℝ → Prop) [DecidablePred p] (y), 0 ≤ R.filter p y := fun p _ y => by
      rw [filter_apply]
      split_ifs
      · exact hR.nonneg y
      · exact le_rfl
    have hmp : 0 ≤ mass Rp := mass_nonneg (hnn _)
    have hmm : 0 ≤ mass Rm := mass_nonneg (hnn _)
    have hm₁ : 0 ≤ mass R₁ := mass_nonneg (hnn _)
    have hmsum : mass Rp + mass Rm + mass R₁ = 1 := by
      have := congrArg mass hdecomp
      rw [mass_add, mass_add, hR.mass_eq_one] at this
      linarith
    have hm₁β : mass R₁ = β := by
      rw [← hR2, mean_snd, mass, sum_eq_sum_of_ne_zero_mem (P := R₁) (s := R.support)
        (fun y hy => mem_support_iff.2 fun h => hy (by simp [hR₁, filter_apply, h])) _
        (fun _ => rfl)]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [hR₁, filter_apply]
      rcases hRsnd y (mem_support_iff.1 hy) with h | h
      · simp [h]
      · simp [h]
    -- The contribution of the bit-`0` states and the sign of the last vector.
    set a := 3 * (mass Rp - mass Rm) with ha
    have ha2 : |a| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    set ε : ℝ := if 0 ≤ a then 1 else -1 with hε
    have hε1 : ε = 1 ∨ ε = -1 := by
      rw [hε]
      split_ifs <;> simp
    have hεa : |ε - a| ≤ 1 := by
      rw [abs_le, hε]
      split_ifs with h
      · constructor <;> linarith [abs_le.1 ha2]
      · constructor <;> linarith [abs_le.1 ha2]
    have hβpos : 0 < 6 * β := by linarith
    set t := 1 / 2 + (ε - a) / (6 * β) with ht
    have ht0 : 0 ≤ t := by
      have : -(1 / 2 : ℝ) ≤ (ε - a) / (6 * β) := by
        rw [le_div_iff₀ hβpos]
        linarith [abs_le.1 hεa]
      rw [ht]
      linarith
    have ht1 : t ≤ 1 := by
      have : (ε - a) / (6 * β) ≤ 1 / 2 := by
        rw [div_le_iff₀ hβpos]
        linarith [abs_le.1 hεa]
      rw [ht]
      linarith
    -- The pullback of `R` to the support of `P`.
    set S : E →₀ ℝ := mapDomain (fun y : E × ℝ => y.1 + (3 : ℝ) • w) Rp +
      mapDomain (fun y : E × ℝ => y.1 - (3 : ℝ) • w) Rm +
      t • mapDomain (fun y : E × ℝ => y.1 + (3 : ℝ) • w) R₁ +
      (1 - t) • mapDomain (fun y : E × ℝ => y.1 - (3 : ℝ) • w) R₁ with hS
    refine ⟨Fin.snoc ε' ε, ?_, S, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hε1
      · simpa using hε' i
    · intro x
      have h1 := mapDomain_apply_nonneg (fun y : E × ℝ => y.1 + (3 : ℝ) • w) (P := Rp) (hnn _) x
      have h2 := mapDomain_apply_nonneg (fun y : E × ℝ => y.1 - (3 : ℝ) • w) (P := Rm) (hnn _) x
      have h3 := mapDomain_apply_nonneg (fun y : E × ℝ => y.1 + (3 : ℝ) • w) (P := R₁) (hnn _) x
      have h4 := mapDomain_apply_nonneg (fun y : E × ℝ => y.1 - (3 : ℝ) • w) (P := R₁) (hnn _) x
      simp only [hS, coe_add, Pi.add_apply, coe_smul, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (add_nonneg (add_nonneg h1 h2) (mul_nonneg ht0 h3))
        (mul_nonneg (by linarith) h4)
    · simp only [hS, mass_add, mass_smul, mass_mapDomain]
      linear_combination hmsum
    · intro x hx
      by_contra! hPx
      apply hx
      have key : ∀ (f : E × ℝ → E) (R' : E × ℝ →₀ ℝ), (∀ y, R' y ≠ 0 → P (f y) ≠ 0) →
          mapDomain f R' x = 0 := fun f R' h => by
        by_contra hne
        obtain ⟨y, hy, rfl⟩ := mem_image.1 (mapDomain_support (mem_support_iff.2 hne))
        exact h y (mem_support_iff.1 hy) hPx
      have hp : ∀ y, Rp y ≠ 0 → P (y.1 + (3 : ℝ) • w) ≠ 0 := by
        intro y hy
        rw [hRp, filter_apply] at hy
        split_ifs at hy with h
        · exact h.2
        · exact absurd rfl hy
      have hm : ∀ y, Rm y ≠ 0 → P (y.1 - (3 : ℝ) • w) ≠ 0 := by
        intro y hy
        rw [hRm, filter_apply] at hy
        split_ifs at hy with h
        · have hQy : Q (y.1, 0) ≠ 0 := by
            have := hRQ y hy
            rwa [show y = (y.1, 0) from Prod.ext rfl h.1] at this
          rcases ne_zero_or_ne_zero_of_bitSplit_apply_zero_ne_zero _ _ hQy with h' | h'
          · exact absurd h.2 h'
          · exact h'
        · exact absurd rfl hy
      have h1 : ∀ y, R₁ y ≠ 0 → P (y.1 + (3 : ℝ) • w) ≠ 0 ∧ P (y.1 - (3 : ℝ) • w) ≠ 0 := by
        intro y hy
        rw [hR₁, filter_apply] at hy
        split_ifs at hy with h
        · have h1 : y.2 = 1 := (hRsnd y hy).resolve_left h
          have hQy : Q (y.1, 1) ≠ 0 := by
            have := hRQ y hy
            rwa [show y = (y.1, 1) from Prod.ext rfl h1] at this
          exact ne_zero_and_ne_zero_of_bitSplit_apply_one_ne_zero _ hP.nonneg hQy
        · exact absurd rfl hy
      simp only [hS, coe_add, Pi.add_apply, coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [key (fun y => y.1 + (3 : ℝ) • w) Rp hp, key (fun y => y.1 - (3 : ℝ) • w) Rm hm,
        key (fun y => y.1 + (3 : ℝ) • w) R₁ (fun y hy => (h1 y hy).1),
        key (fun y => y.1 - (3 : ℝ) • w) R₁ (fun y hy => (h1 y hy).2)]
      ring
    · have hcoef : (mass Rp - mass Rm + (2 * t - 1) * mass R₁) * 3 = ε := by
        have hdiv : (ε - a) / (6 * β) * (6 * β) = ε - a := div_mul_cancel₀ _ hβpos.ne'
        rw [hm₁β, ht]
        linear_combination hdiv - ha
      have hμ : (mean R).1 = Rp.sum (fun y p => p • y.1) + Rm.sum (fun y p => p • y.1) +
          R₁.sum (fun y p => p • y.1) := by
        rw [mean_fst]
        conv_lhs => rw [hdecomp]
        rw [sum_add_index' (h := fun (y : E × ℝ) (p : ℝ) => p • y.1) (fun _ => zero_smul ℝ _)
          (fun _ _ _ => add_smul _ _ _),
          sum_add_index' (h := fun (y : E × ℝ) (p : ℝ) => p • y.1) (fun _ => zero_smul ℝ _)
          (fun _ _ _ => add_smul _ _ _)]
      have hgoal : mean S = (Rp.sum (fun y p => p • y.1) + Rm.sum (fun y p => p • y.1) +
          R₁.sum (fun y p => p • y.1)) + ((mass Rp - mass Rm + (2 * t - 1) * mass R₁) * 3) • w := by
        simp only [hS, mean_add, mean_smul, mean_mapDomain_add_const, mean_mapDomain_sub_const]
        module
      rw [hgoal, ← hμ, hR1, hcoef, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, ← hw]
      abel

end Balancing

end Finsupp
