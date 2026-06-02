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
# Erdős Problem 18

*Reference:*
* [erdosproblems.com/18](https://www.erdosproblems.com/18)
* [ErGr80] Erdős, P. and Graham, R. L. (1980). Old and New Problems and Results in Combinatorial Number
Theory. Monographies de L'Enseignement Mathématique, 28. Université de Genève. (See the
sections on Egyptian fractions or practical numbers).
* [Vo85] Vose, Michael D., Egyptian fractions. Bull. London Math. Soc. (1985), 21-24.
-/

open Filter Asymptotics Real

namespace Erdos18

/-- For a practical number $n$, $h(n)$ is the maximum over all $1 ≤ m ≤ n$ of
the minimum number of divisors of $n$ needed to represent $m$ as a sum of
distinct divisors. -/
noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

/- ### Examples for `practicalH` -/

/-- $h(1) = 1$: we need the single divisor {1} to represent 1. -/
@[category test, AMS 11]
theorem practicalH_one : practicalH 1 = 1 := by
  norm_num [subsetSums, practicalH]

/-- $h(2) = 1$: divisors are {1, 2}, each of m=1,2 needs only 1 divisor. -/
@[category test, AMS 11]
theorem practicalH_two : practicalH 2 = 1 := by
  simp only [practicalH, (by decide : Finset.Icc 1 2 = ({1, 2} : Finset ℕ)),
    (by decide : Nat.divisors 2 = ({1, 2} : Finset ℕ)), Finset.sup_insert, Finset.sup_singleton]
  have h1 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2} ∧ D.card = k ∧ 1 ∈ subsetSums D} = 1 :=
    le_antisymm (Nat.sInf_le ⟨{1}, by simp, rfl, {1}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {1}, by simp, rfl, {1}, rfl.subset, by simp⟩ fun k ⟨D, _, hD, B, hB, hm⟩ =>
        hD ▸ Finset.one_le_card.mpr ((Finset.nonempty_iff_ne_empty.mpr fun h => by simp [h] at hm).mono hB))
  have h2 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2} ∧ D.card = k ∧ 2 ∈ subsetSums D} = 1 :=
    le_antisymm (Nat.sInf_le ⟨{2}, by simp, rfl, {2}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {2}, by simp, rfl, {2}, rfl.subset, by simp⟩ fun k ⟨D, _, hD, B, hB, hm⟩ =>
        hD ▸ Finset.one_le_card.mpr ((Finset.nonempty_iff_ne_empty.mpr fun h => by simp [h] at hm).mono hB))
  simp [h1, h2]

/-- $h(6) = 2$: divisors are {1, 2, 3, 6}. The hardest m to represent is
m=4 or m=5, each requiring 2 divisors: 4=1+3, 5=2+3. -/
@[category test, AMS 11]
theorem practicalH_six : practicalH 6 = 2 := by
  sorry

/-- $h(12) = 3$: divisors are {1, 2, 3, 4, 6, 12}. The hardest m is
m=11, requiring 3 divisors: 11=1+4+6. -/
@[category test, AMS 11]
theorem practicalH_twelve : practicalH 12 = 3 := by
  sorry

private def hasFinsetSubsetSum (D : Finset ℕ) (m : ℕ) : Prop :=
  ∃ B ∈ D.powerset, B.sum id = m

private instance (D : Finset ℕ) (m : ℕ) : Decidable (hasFinsetSubsetSum D m) := by
  unfold hasFinsetSubsetSum
  infer_instance

private lemma hasFinsetSubsetSum_iff_mem_subsetSums {D : Finset ℕ} {m : ℕ} :
    hasFinsetSubsetSum D m ↔ m ∈ subsetSums (D : Set ℕ) := by
  unfold hasFinsetSubsetSum
  constructor
  · rintro ⟨B, hBpow, hsum⟩
    rw [Finset.mem_powerset] at hBpow
    exact ⟨B, by exact_mod_cast hBpow, hsum.symm⟩
  · rintro ⟨B, hBsub, hsum⟩
    refine ⟨B, ?_, hsum.symm⟩
    rw [Finset.mem_powerset]
    exact_mod_cast hBsub

private def canSumAtMost : List ℕ → ℕ → ℕ → Bool
  | _, _, 0 => true
  | [], _, _ => false
  | _ :: _, 0, _ => false
  | x :: xs, k + 1, t =>
      canSumAtMost xs (k + 1) t || (x ≤ t && canSumAtMost xs k (t - x))

private lemma canSumAtMost_of_sublist {ys xs : List ℕ} (hsub : ys.Sublist xs) :
    ∀ {k t : ℕ}, ys.length ≤ k → ys.sum = t → canSumAtMost xs k t = true := by
  induction hsub with
  | slnil =>
      intro k t hlen hsum
      subst t
      simp [canSumAtMost]
  | @cons l₁ l₂ x hsub ih =>
      intro k t hlen hsum
      cases t with
      | zero => simp [canSumAtMost]
      | succ t' =>
          cases k with
          | zero =>
              have : l₁ = [] := by
                exact List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
              simp [this] at hsum
          | succ k =>
              simp [canSumAtMost]
              exact Or.inl (ih hlen hsum)
  | @cons₂ l₁ l₂ x hsub ih =>
      intro k t hlen hsum
      cases t with
      | zero =>
          simp [canSumAtMost]
      | succ t' =>
          cases k with
          | zero =>
              simp at hlen
          | succ k =>
              simp at hsum
              simp [canSumAtMost]
              right
              constructor
              · omega
              · apply ih
                · simpa using Nat.succ_le_succ_iff.mp hlen
                · omega

private lemma filter_toFinset_eq_of_subset {xs : List ℕ} {D : Finset ℕ}
    (hD : D ⊆ xs.toFinset) :
    (xs.filter (fun x => x ∈ D)).toFinset = D := by
  ext x
  simp only [List.mem_toFinset, List.mem_filter]
  constructor
  · exact fun hx => of_decide_eq_true hx.2
  · intro hx
    exact ⟨by simpa using hD hx, by simpa using hx⟩

private lemma filter_length_eq_card_of_subset {xs : List ℕ} (hxs : xs.Nodup)
    {D : Finset ℕ} (hD : D ⊆ xs.toFinset) :
    (xs.filter (fun x => x ∈ D)).length = D.card := by
  have hEq := filter_toFinset_eq_of_subset (xs := xs) (D := D) hD
  have hnodup : (xs.filter (fun x => x ∈ D)).Nodup := hxs.filter _
  have hcard := congrArg Finset.card hEq
  rw [← hcard]
  exact (List.toFinset_card_of_nodup hnodup).symm

private lemma filter_sum_eq_sum_of_subset {xs : List ℕ} (hxs : xs.Nodup)
    {D : Finset ℕ} (hD : D ⊆ xs.toFinset) :
    (xs.filter (fun x => x ∈ D)).sum = D.sum id := by
  have hEq := filter_toFinset_eq_of_subset (xs := xs) (D := D) hD
  have hnodup : (xs.filter (fun x => x ∈ D)).Nodup := hxs.filter _
  have hsum := List.sum_toFinset id hnodup
  simp at hsum
  have hEq' : {x ∈ xs.toFinset | x ∈ D} = D := by
    simpa using hEq
  rw [hEq'] at hsum
  exact hsum.symm

private lemma canSumAtMost_of_finset_subset {xs : List ℕ} (hxs : xs.Nodup)
    {D : Finset ℕ} (hD : D ⊆ xs.toFinset) {k t : ℕ}
    (hcard : D.card ≤ k) (hsum : D.sum id = t) :
    canSumAtMost xs k t = true := by
  let ys := xs.filter (fun x => x ∈ D)
  apply canSumAtMost_of_sublist (List.filter_sublist (p := fun x => x ∈ D))
  · dsimp [ys]
    rw [filter_length_eq_card_of_subset hxs hD]
    exact hcard
  · dsimp [ys]
    rw [filter_sum_eq_sum_of_subset hxs hD]
    exact hsum

private lemma canSumAtMost_sound {xs : List ℕ} (hxs : xs.Nodup) :
    ∀ {k t : ℕ}, canSumAtMost xs k t = true →
      ∃ D : Finset ℕ, D ⊆ xs.toFinset ∧ D.card ≤ k ∧ D.sum id = t := by
  induction xs with
  | nil =>
      intro k t h
      cases t with
      | zero =>
          exact ⟨∅, by simp, by simp, by simp⟩
      | succ t' =>
          simp [canSumAtMost] at h
  | cons x xs ih =>
      intro k t h
      cases t with
      | zero =>
          exact ⟨∅, by simp, by simp, by simp⟩
      | succ t' =>
          cases k with
          | zero =>
              simp [canSumAtMost] at h
          | succ k =>
              simp at hxs
              simp [canSumAtMost] at h
              rcases h with h | h
              · obtain ⟨D, hD, hcard, hsum⟩ := ih hxs.2 h
                refine ⟨D, ?_, hcard, hsum⟩
                intro y hy
                simp [hD hy]
              · obtain ⟨hxle, hcan⟩ := h
                obtain ⟨D, hD, hcard, hsum⟩ := ih hxs.2 hcan
                have hxnotD : x ∉ D := by
                  intro hxD
                  exact hxs.1 (by simpa using hD hxD)
                refine ⟨insert x D, ?_, ?_, ?_⟩
                · intro y hy
                  simp at hy ⊢
                  rcases hy with rfl | hy
                  · simp
                  · exact Or.inr (by simpa using hD hy)
                · rw [Finset.card_insert_of_notMem hxnotD]
                  omega
                · rw [Finset.sum_insert hxnotD, hsum]
                  simp only [id_eq]
                  omega

private lemma practicalH_eq_of_subset_sum_certificate (n K hard : ℕ)
    (hhard : hard ∈ Finset.Icc 1 n)
    (hupper : ∀ m ∈ Finset.Icc 1 n,
      ∃ D ∈ n.divisors.powerset, D.card ≤ K ∧ hasFinsetSubsetSum D m)
    (hlower : ∀ D ∈ n.divisors.powerset, D.card ≤ K - 1 →
      ¬ hasFinsetSubsetSum D hard) :
    practicalH n = K := by
  unfold practicalH
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro m hm
    rcases hupper m hm with ⟨D, hDpow, hDcard, hsum⟩
    have hDsub : D ⊆ n.divisors := by
      simpa [Finset.mem_powerset] using hDpow
    have hmem : D.card ∈ ({k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧
        m ∈ subsetSums (D : Set ℕ)} : Set ℕ) := by
      exact ⟨D, hDsub, rfl, hasFinsetSubsetSum_iff_mem_subsetSums.mp hsum⟩
    exact (Nat.sInf_le hmem).trans hDcard
  · have hhard_nonempty : ({k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧
        hard ∈ subsetSums (D : Set ℕ)} : Set ℕ).Nonempty := by
      rcases hupper hard hhard with ⟨D, hDpow, _hDcard, hsum⟩
      have hDsub : D ⊆ n.divisors := by
        simpa [Finset.mem_powerset] using hDpow
      exact ⟨D.card, D, hDsub, rfl, hasFinsetSubsetSum_iff_mem_subsetSums.mp hsum⟩
    have hlower_sInf : K ≤ sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧
        hard ∈ subsetSums (D : Set ℕ)} := by
      apply le_csInf hhard_nonempty
      intro k hk
      rcases hk with ⟨D, hDsub, hDcard, hsum⟩
      by_contra hnot
      have hDpow : D ∈ n.divisors.powerset := by
        simpa [Finset.mem_powerset] using hDsub
      have hDcard_le : D.card ≤ K - 1 := by omega
      exact hlower D hDpow hDcard_le (hasFinsetSubsetSum_iff_mem_subsetSums.mpr hsum)
    exact hlower_sInf.trans (Finset.le_sup (s := Finset.Icc 1 n)
      (f := fun m => sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧
          m ∈ subsetSums (D : Set ℕ)}) hhard)

private lemma practicalH_eq_of_subset_sum_bounds (n K hard : ℕ)
    (hhard : hard ∈ Finset.Icc 1 n)
    (hupper : ∀ m ∈ Finset.Icc 1 n,
      ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card ≤ K ∧ hasFinsetSubsetSum D m)
    (hlower : ∀ D : Finset ℕ, D ⊆ n.divisors → D.card ≤ K - 1 →
      ¬ hasFinsetSubsetSum D hard) :
    practicalH n = K := by
  unfold practicalH
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro m hm
    rcases hupper m hm with ⟨D, hDsub, hDcard, hsum⟩
    have hmem : D.card ∈ ({k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧
        m ∈ subsetSums (D : Set ℕ)} : Set ℕ) := by
      exact ⟨D, hDsub, rfl, hasFinsetSubsetSum_iff_mem_subsetSums.mp hsum⟩
    exact (Nat.sInf_le hmem).trans hDcard
  · have hhard_nonempty : ({k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧
        hard ∈ subsetSums (D : Set ℕ)} : Set ℕ).Nonempty := by
      rcases hupper hard hhard with ⟨D, hDsub, _hDcard, hsum⟩
      exact ⟨D.card, D, hDsub, rfl, hasFinsetSubsetSum_iff_mem_subsetSums.mp hsum⟩
    have hlower_sInf : K ≤ sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧
        hard ∈ subsetSums (D : Set ℕ)} := by
      apply le_csInf hhard_nonempty
      intro k hk
      rcases hk with ⟨D, hDsub, hDcard, hsum⟩
      by_contra hnot
      have hDcard_le : D.card ≤ K - 1 := by omega
      exact hlower D hDsub hDcard_le (hasFinsetSubsetSum_iff_mem_subsetSums.mpr hsum)
    exact hlower_sInf.trans (Finset.le_sup (s := Finset.Icc 1 n)
      (f := fun m => sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧
          m ∈ subsetSums (D : Set ℕ)}) hhard)

/-- $h(56) = 5$: the hard value is `55`, which needs five divisors of `56`. -/
@[category test, AMS 11]
theorem practicalH_fiftysix : practicalH 56 = 5 := by
  apply practicalH_eq_of_subset_sum_certificate 56 5 55
  · decide
  · native_decide
  · native_decide

private def divisors7200 : List ℕ :=
  [7200, 3600, 2400, 1800, 1440, 1200, 900, 800, 720, 600, 480, 450, 400, 360, 300, 288,
   240, 225, 200, 180, 160, 150, 144, 120, 100, 96, 90, 80, 75, 72, 60, 50, 48, 45, 40,
   36, 32, 30, 25, 24, 20, 18, 16, 15, 12, 10, 9, 8, 6, 5, 4, 3, 2, 1]

private def divisors120 : List ℕ :=
  [120, 60, 40, 30, 24, 20, 15, 12, 10, 8, 6, 5, 4, 3, 2, 1]

private def smallDivisors7200 : List ℕ :=
  [50, 48, 45, 40, 36, 32, 30, 25, 24, 20, 18, 16, 15, 12, 10, 9, 8, 6, 5, 4, 3, 2, 1]

private lemma hasFinsetSubsetSum_self {D : Finset ℕ} {m : ℕ} (hsum : D.sum id = m) :
    hasFinsetSubsetSum D m :=
  ⟨D, by simp, hsum⟩

private lemma subset_sum_7200_upper (m : ℕ) (hm : m ∈ Finset.Icc 1 7200) :
    ∃ D : Finset ℕ, D ⊆ Nat.divisors 7200 ∧ D.card ≤ 6 ∧ hasFinsetSubsetSum D m := by
  let q := m / 60
  let r := m % 60
  have hmle : m ≤ 7200 := (Finset.mem_Icc.mp hm).2
  have hqmem : q ∈ Finset.Icc 0 120 := by
    simp [q]
    omega
  have hrmem : r ∈ Finset.Icc 0 59 := by
    simp [r]
    have := Nat.mod_lt m (by norm_num : 0 < 60)
    omega
  have hqcan : canSumAtMost divisors120 4 q = true :=
    (by native_decide : ∀ q ∈ Finset.Icc 0 120, canSumAtMost divisors120 4 q = true) q hqmem
  have hrcan : canSumAtMost smallDivisors7200 2 r = true :=
    (by native_decide : ∀ r ∈ Finset.Icc 0 59, canSumAtMost smallDivisors7200 2 r = true) r hrmem
  obtain ⟨Q, hQsub, hQcard, hQsum⟩ :=
    canSumAtMost_sound (by native_decide : divisors120.Nodup) hqcan
  obtain ⟨R, hRsub, hRcard, hRsum⟩ :=
    canSumAtMost_sound (by native_decide : smallDivisors7200.Nodup) hrcan
  let scaled := Q.image (fun d => 60 * d)
  let D := scaled ∪ R
  have hscaled_sub_univ : scaled ⊆ (divisors120.toFinset.image fun d => 60 * d) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨d, hd, rfl⟩
    exact Finset.mem_image.mpr ⟨d, hQsub hd, rfl⟩
  have hscaled_sub : scaled ⊆ Nat.divisors 7200 := by
    intro x hx
    have hx' : x ∈ (divisors120.toFinset.image fun d => 60 * d) := hscaled_sub_univ hx
    have hcert :
        (divisors120.toFinset.image fun d => 60 * d) ⊆ Nat.divisors 7200 := by native_decide
    exact hcert hx'
  have hR_sub : R ⊆ Nat.divisors 7200 := by
    intro x hx
    have hx' : x ∈ smallDivisors7200.toFinset := hRsub hx
    have hcert : smallDivisors7200.toFinset ⊆ Nat.divisors 7200 := by native_decide
    exact hcert hx'
  have hdisj_univ :
      Disjoint (divisors120.toFinset.image fun d => 60 * d) smallDivisors7200.toFinset := by
    native_decide
  have hdisj : Disjoint scaled R := hdisj_univ.mono hscaled_sub_univ hRsub
  have hscaled_sum : scaled.sum id = 60 * q := by
    dsimp [scaled]
    rw [Finset.sum_image]
    · simp only [id_eq]
      rw [← Finset.mul_sum]
      have hQsum' : (∑ i ∈ Q, i) = q := by
        simpa [id_eq] using hQsum
      rw [hQsum']
    · intro a _ b _ hab
      change 60 * a = 60 * b at hab
      omega
  refine ⟨D, ?_, ?_, ?_⟩
  · intro x hx
    dsimp [D] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hscaled_sub hx
    · exact hR_sub hx
  · dsimp [D]
    have hcard_union := Finset.card_union_le scaled R
    have hscaled_card : scaled.card ≤ Q.card := by
      dsimp [scaled]
      exact Finset.card_image_le
    omega
  · apply hasFinsetSubsetSum_self
    dsimp [D]
    rw [Finset.sum_union hdisj, hscaled_sum, hRsum]
    have hdiv := Nat.div_add_mod m 60
    dsimp [q, r]
    omega

/-- $h(7200) = 6$.  The upper bound uses `7200 = 60 * 120`;
the hard value is `6667`. -/
@[category test, AMS 11]
theorem practicalH_7200 : practicalH 7200 = 6 := by
  apply practicalH_eq_of_subset_sum_bounds 7200 6 6667
  · exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  · exact subset_sum_7200_upper
  · intro D hDsub hDcard hsum
    rcases hsum with ⟨B, hBpow, hBsum⟩
    rw [Finset.mem_powerset] at hBpow
    have hBsub_divs : B ⊆ divisors7200.toFinset := by
      have hdivs : Nat.divisors 7200 = divisors7200.toFinset := by native_decide
      intro x hx
      rw [← hdivs]
      exact hDsub (hBpow hx)
    have hBcard : B.card ≤ 5 := by
      have hBcard_le : B.card ≤ D.card := Finset.card_le_card hBpow
      omega
    have hcan := canSumAtMost_of_finset_subset
      (by native_decide : divisors7200.Nodup) hBsub_divs hBcard hBsum
    have hfalse : canSumAtMost divisors7200 5 6667 = false := by native_decide
    rw [hfalse] at hcan
    contradiction

/-- For any practical number $n$, $h(n) ≤ number of divisors of $n$. -/
@[category test, AMS 11]
theorem practicalH_le_divisors (n : ℕ) (hn : Nat.IsPractical n) :
    practicalH n ≤ n.divisors.card := by
  simp only [practicalH, Finset.sup_le_iff, Finset.mem_Icc]
  exact fun m ⟨_, hm⟩ => Nat.sInf_le ⟨n.divisors, Finset.Subset.refl _, rfl, hn m hm⟩

/-- $h(n!)$ is well-defined since $n!$ is practical for $n ≥ 1$. -/
@[category textbook, AMS 11]
theorem factorial_isPractical (n : ℕ) : Nat.IsPractical n.factorial := by
    induction n with
  | zero =>
    intro m hm; simp at hm; interval_cases m
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp⟩
  | succ n ih =>
    intro m hm
    by_cases hle : m ≤ n.factorial
    · exact subsetSums_mono (by exact_mod_cast (Nat.divisors_subset_of_dvd
        (Nat.factorial_ne_zero _) (Nat.factorial_dvd_factorial n.le_succ))) (ih m hle)
    · push_neg at hle; rw [Nat.factorial_succ] at hm
      set q := m / (n + 1); set r := m % (n + 1)
      have h_div : m = (n + 1) * q + r := (Nat.div_add_mod m (n + 1)).symm
      have h_r_lt : r < n + 1 := Nat.mod_lt m (Nat.succ_pos n)
      obtain ⟨B, hB_sub, hB_sum⟩ := ih q (Nat.div_le_of_le_mul (by linarith))
      have hdvd : ∀ d ∈ B, d * (n + 1) ∈ (n + 1).factorial.divisors := fun d hd => by
        refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero _⟩
        rw [mul_comm, Nat.factorial_succ]
        exact mul_dvd_mul_left _ (Nat.dvd_of_mem_divisors (by exact_mod_cast hB_sub hd))
      have hB'_sum : (B.image (· * (n + 1))).sum id = (n + 1) * q := by
        rw [Finset.sum_image (fun a _ b _ h => mul_right_cancel₀ (by omega) h)]
        simp [Finset.mul_sum, mul_comm, hB_sum]
      by_cases hr : r = 0
      · rw [show m = (B.image (· * (n + 1))).sum id from by rw [hB'_sum]; omega]
        exact ⟨_, fun x hx => by
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx; exact hdvd d hd, rfl⟩
      · have h_disj : Disjoint (B.image (· * (n + 1))) {r} := by
          rw [Finset.disjoint_singleton_right, Finset.mem_image]; rintro ⟨d, hd, hdr⟩
          have : 0 < d := Nat.pos_of_dvd_of_pos
            (Nat.dvd_of_mem_divisors (by exact_mod_cast hB_sub hd)) (Nat.factorial_pos n)
          have := le_mul_of_one_le_left (Nat.zero_le (n + 1)) this
          omega
        rw [show m = (B.image (· * (n + 1)) ∪ {r}).sum id from by
          rw [Finset.sum_union h_disj, Finset.sum_singleton, hB'_sum, id_eq]; exact h_div]
        exact ⟨_, fun x hx => by
          rcases Finset.mem_union.mp hx with h | h
          · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp h; exact hdvd d hd
          · rw [Finset.mem_singleton.mp h]; exact Nat.mem_divisors.mpr
              ⟨(Nat.dvd_factorial (by omega) (by omega)).trans
                (Nat.factorial_dvd_factorial n.le_succ), Nat.factorial_ne_zero _⟩, rfl⟩

/- ### Erdős's Conjectures -/

/--
**Conjecture 1.**
Are there infinitely many practical numbers $m$ such that $h(m) < (\log \log m)^{O(1)}$?

More precisely: does there exist a constant $C > 0$ such that for infinitely many
practical numbers $m$, we have $h(m) < (\log \log m)^C$?
-/
@[category research open, AMS 11]
theorem erdos_18a : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧ ∃ᶠ m in atTop, Nat.IsPractical m ∧
      (practicalH m : ℝ) < (log (log m)) ^ C := by
  sorry

/--
**Conjecture 2.**
Is it true that $h(n!) < n^{o(1)}$? That is, for all $\varepsilon > 0$,
is $h(n!) < n^\varepsilon$ for sufficiently large $n$?
-/
@[category research open, AMS 11]
theorem erdos_18b : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (practicalH n.factorial : ℝ) < (n : ℝ) ^ ε := by
  sorry

/--
**Conjecture 3.**
Or perhaps even $h(n!) < (\log n)^{O(1)}$?

Erdős offered \$250 for a proof or disproof.
-/
@[category research open, AMS 11]
theorem erdos_18c : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (practicalH n.factorial : ℝ) < (log n) ^ C := by
  sorry

/--
**Erdős's Theorem.**
Erdős proved that $h(n!) < n$ for all $n \ge 1$.
-/
@[category research solved, AMS 11]
theorem erdos_18_upper_bound :
    ∀ᶠ n : ℕ in atTop, practicalH (Nat.factorial n) < n := by
  sorry

/--
**Vose's Theorem.**
Vose proved the existence of infinitely many practical numbers $m$ such that
$h(m) \ll (\log m)^{1/2}$. This gives a positive answer to a weaker form of Conjecture 1.
-/
@[category research solved, AMS 11]
theorem erdos_18_vose :
    ∃ C : ℝ, 0 < C ∧ ∃ᶠ m in atTop, Nat.IsPractical m ∧
      (practicalH m : ℝ) < C * (log m) ^ (1 / 2 : ℝ) := by
  sorry

end Erdos18
