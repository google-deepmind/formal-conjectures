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
# Erdős Problem 201

*Reference:* [erdosproblems.com/201](https://www.erdosproblems.com/201)
-/

@[expose] public section

namespace Erdos201

open Filter
open scoped Topology

/-- $R_k(N)$ is the largest size of a progression-free subset of $\{1,\ldots,N\}$. -/
noncomputable def R (k N : ℕ) : ℕ :=
  (Finset.Icc (1 : ℤ) N).maxAPFreeCard k

/-- $G_k(N)$ is the sharp progression-free subset-size guarantee for arbitrary
sets of $N$ integers. -/
noncomputable def G (k N : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ s : Finset ℤ, s.card = N ∧ s.maxAPFreeCard k = m}

/-- Let $G_k(N)$ be such that any set of $N$ integers contains a subset of size at least
$G_k(N)$ which does not contain a $k$-term arithmetic progression. Determine the size of $G_k(N)$.
How does it relate to $R_k(N)$, the size of the largest subset of $\{1,\ldots,N\}$
without a $k$-term arithmetic progression? -/
@[category research open, AMS 5 11]
theorem erdos_201.parts.i : answer(sorry) = G := by
  sorry

/-- Is it true that $\lim_{N\to\infty} R_3(N)/G_3(N)=1$? -/
@[category research open, AMS 5 11]
theorem erdos_201.parts.ii :
    answer(sorry) ↔ Tendsto (fun N : ℕ => (R 3 N : ℝ) / (G 3 N : ℝ)) atTop (𝓝 1) := by
  sorry

/-- An integer interval $\{1,\ldots,N\}$ has $N$ elements, including when $N=0$. -/
@[category API, AMS 5 11]
theorem interval_card (N : ℕ) : (Finset.Icc (1 : ℤ) N).card = N := by
  simp

/-- The largest progression-free subset has size at most that of its ambient set. -/
@[category API, AMS 5 11]
theorem maxAPFreeCard_le_card (k : ℕ) (s : Finset ℤ) : s.maxAPFreeCard k ≤ s.card := by
  classical
  unfold Finset.maxAPFreeCard
  apply Finset.sup_le
  intro t ht
  exact Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1)

/-- A progression-free subset provides a lower bound for the extremal size. -/
@[category API, AMS 5 11]
theorem card_le_maxAPFreeCard {k : ℕ} {s t : Finset ℤ} (hts : t ⊆ s)
    (ht : (t : Set ℤ).IsAPOfLengthFree k) : t.card ≤ s.maxAPFreeCard k := by
  classical
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hts, ht⟩)

/-- The infimum defining $G_k(N)$ is taken over a nonempty collection. -/
@[category API, AMS 5 11]
theorem G_values_nonempty (k N : ℕ) :
    {m : ℕ | ∃ s : Finset ℤ, s.card = N ∧ s.maxAPFreeCard k = m}.Nonempty :=
  ⟨R k N, Finset.Icc 1 N, interval_card N, rfl⟩

/-- Every $N$-element set has extremal subset size at least $G_k(N)$. -/
@[category API, AMS 5 11]
theorem G_le_maxAPFreeCard {k N : ℕ} {s : Finset ℤ} (hs : s.card = N) :
    G k N ≤ s.maxAPFreeCard k := by
  exact csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ⟨s, hs, rfl⟩

/-- It is trivial that $G_k(N)\leq R_k(N)$. -/
@[category research solved, AMS 5 11]
theorem erdos_201.variants.G_le_R (k N : ℕ) : G k N ≤ R k N :=
  G_le_maxAPFreeCard (interval_card N)

/-- $R_k(N)$ is bounded above by $N$. -/
@[category API, AMS 5 11]
theorem R_le (k N : ℕ) : R k N ≤ N := by
  exact (maxAPFreeCard_le_card k _).trans_eq (interval_card N)

/-- Three distinct integers with the middle term equal to their average form a $3$-term AP. -/
@[category API, AMS 5 11]
theorem isAPOfLength_triple {a b c : ℤ} (hab : a ≠ b) (h : a + c = b + b) :
    ({a, b, c} : Set ℤ).IsAPOfLength 3 := by
  have hbc : b ≠ c := by omega
  have hac : a ≠ c := by omega
  refine ⟨a, b - a, ?_, ?_⟩
  · simp [hab, hac, hbc]
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
      · refine ⟨2, by norm_num, ?_⟩
        simp only [nsmul_eq_mul]
        omega
    · rintro ⟨i, hi, hz⟩
      have hi' : i < 3 := by exact_mod_cast hi
      interval_cases i <;> simp_all
      all_goals omega

/-- The repository's $3$-term AP-free predicate agrees with Mathlib's `ThreeAPFree`. -/
@[category API, AMS 5 11]
theorem isAPOfLengthFree_three_iff (s : Set ℤ) :
    s.IsAPOfLengthFree 3 ↔ ThreeAPFree s := by
  constructor
  · intro hs a ha b hb c hc h
    by_contra hab
    have ht : ({a, b, c} : Set ℤ) ⊆ s := by
      intro z hz
      rcases hz with rfl | rfl | rfl <;> assumption
    have hle := hs _ ht (isAPOfLength_triple hab h)
    norm_num at hle
  · intro hs t ht hAP
    obtain ⟨a, d, hcard, heq⟩ := hAP
    have hmem (i : ℕ) (hi : i < 3) : a + i • d ∈ s := by
      apply ht
      rw [heq]
      exact ⟨i, by exact_mod_cast hi, rfl⟩
    have h := hs (hmem 0 (by omega)) (hmem 1 (by omega)) (hmem 2 (by omega)) (by
      simp; ring)
    have hd : d = 0 := by simpa using h.symm
    have hex : ∃ i : ℕ, i < 3 := ⟨0, by norm_num⟩
    simp [hd, hex] at heq
    rw [heq] at hcard
    simp at hcard

/-- The extremal size for three-term progressions is Mathlib's additive Roth number. -/
@[category API, AMS 5 11]
theorem maxAPFreeCard_three (s : Finset ℤ) : s.maxAPFreeCard 3 = addRothNumber s := by
  classical
  apply le_antisymm
  · unfold Finset.maxAPFreeCard
    apply Finset.sup_le
    intro t ht
    obtain ⟨hts, ht⟩ := Finset.mem_filter.mp ht
    exact ((isAPOfLengthFree_three_iff _).mp ht).le_addRothNumber
      (Finset.mem_powerset.mp hts)
  · obtain ⟨t, hts, hcard, ht⟩ := addRothNumber_spec s
    rw [← hcard]
    exact card_le_maxAPFreeCard hts ((isAPOfLengthFree_three_iff _).mpr ht)

/-- A sorted triple is progression-free precisely when its middle is not the average. -/
@[category API, AMS 5 11]
theorem threeAPFree_triple {a b c : ℤ} (hab : a < b) (hbc : b < c)
    (hne : a + c ≠ b + b) : ThreeAPFree ({a, b, c} : Set ℤ) := by
  simp only [ThreeAPFree, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- A non-averaging sorted triple provides three progression-free elements. -/
@[category API, AMS 5 11]
theorem three_le_maxAPFreeCard {s : Finset ℤ} {a b c : ℤ}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a < b) (hbc : b < c)
    (hne : a + c ≠ b + b) : 3 ≤ s.maxAPFreeCard 3 := by
  have hcard : ({a, b, c} : Finset ℤ).card = 3 := by
    simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)]
  have hts : ({a, b, c} : Finset ℤ) ⊆ s := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using ⟨ha, hb, hc⟩
  have ht : (({a, b, c} : Finset ℤ) : Set ℤ).IsAPOfLengthFree 3 := by
    apply (isAPOfLengthFree_three_iff _).mpr
    simpa only [Finset.coe_insert, Finset.coe_singleton] using threeAPFree_triple hab hbc hne
  simpa only [hcard] using card_le_maxAPFreeCard hts ht

/-- Every set of five integers contains a progression-free triple. -/
@[category API, AMS 5 11]
theorem three_le_maxAPFreeCard_of_card_five {s : Finset ℤ} (hs : s.card = 5) :
    3 ≤ s.maxAPFreeCard 3 := by
  let e := s.orderEmbOfFin hs
  have hab : e 0 < e 1 := e.strictMono (by decide)
  have hbc : e 1 < e 2 := e.strictMono (by decide)
  have hcd : e 2 < e 4 := e.strictMono (by decide)
  have hm (i : Fin 5) : e i ∈ s := s.orderEmbOfFin_mem hs i
  by_cases h : e 0 + e 4 = e 1 + e 1
  · exact three_le_maxAPFreeCard (hm 0) (hm 2) (hm 4) (hab.trans hbc) hcd (by omega)
  · exact three_le_maxAPFreeCard (hm 0) (hm 1) (hm 4) hab (hbc.trans hcd) h

/-- Every five-element set admits a progression-free subset of size at least three. -/
@[category API, AMS 5 11]
theorem three_le_G_three_five : 3 ≤ G 3 5 := by
  apply le_csInf (G_values_nonempty 3 5)
  rintro m ⟨s, hs, rfl⟩
  exact three_le_maxAPFreeCard_of_card_five hs

/-- The empty set contains no nontrivial progression. -/
@[category API, AMS 5 11]
theorem empty_isAPOfLengthFree (k : ℕ) : (∅ : Set ℤ).IsAPOfLengthFree k := by
  intro t ht hAP
  have hcard := hAP.card
  rw [Set.subset_empty_iff.mp ht] at hcard
  have hk : (k : ℕ∞) = 0 := by simpa using hcard.symm
  exact hk.le.trans (by norm_num)

/-- The maximum progression-free subset size is attained. -/
@[category API, AMS 5 11]
theorem maxAPFreeCard_spec (k : ℕ) (s : Finset ℤ) :
    ∃ t ⊆ s, (t : Set ℤ).IsAPOfLengthFree k ∧ t.card = s.maxAPFreeCard k := by
  classical
  have hne : (s.powerset.filter fun t : Finset ℤ => (t : Set ℤ).IsAPOfLengthFree k).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
      by simpa using empty_isAPOfLengthFree k⟩⟩
  obtain ⟨t, ht, hcard⟩ := Finset.sup_mem_of_nonempty (f := Finset.card) hne
  obtain ⟨hts, hfree⟩ := Finset.mem_filter.mp ht
  exact ⟨t, Finset.mem_powerset.mp hts, hfree, hcard⟩

/-- A worst-case $N$-element set exists, so the universal guarantee is sharp. -/
@[category API, AMS 5 11]
theorem G_attained (k N : ℕ) : ∃ s : Finset ℤ, s.card = N ∧ s.maxAPFreeCard k = G k N :=
  csInf_mem (G_values_nonempty k N)

/-- The extremal definition of $G_k(N)$ agrees with the universal subset-size guarantee. -/
@[category API, AMS 5 11]
theorem le_G_iff (k N m : ℕ) : m ≤ G k N ↔ ∀ s : Finset ℤ, s.card = N →
    ∃ t ⊆ s, (t : Set ℤ).IsAPOfLengthFree k ∧ m ≤ t.card := by
  constructor
  · intro hm s hs
    obtain ⟨t, ht, hfree, hcard⟩ := maxAPFreeCard_spec k s
    exact ⟨t, ht, hfree, hcard ▸ hm.trans (G_le_maxAPFreeCard hs)⟩
  · intro hm
    obtain ⟨s, hs, hG⟩ := G_attained k N
    obtain ⟨t, ht, hfree, hcard⟩ := hm s hs
    exact hcard.trans ((card_le_maxAPFreeCard ht hfree).trans_eq hG)

/-- A singleton contains no nontrivial progression. -/
@[category API, AMS 5 11]
theorem singleton_isAPOfLengthFree (a : ℤ) (k : ℕ) :
    ({a} : Set ℤ).IsAPOfLengthFree k := by
  intro t ht hAP
  have h := Set.encard_mono ht
  rw [show t.encard = (k : ℕ∞) from hAP.card] at h
  simpa using h

/-- For $N>0$, the guarantee is positive; the denominator of the proposed limit is nonzero. -/
@[category API, AMS 5 11]
theorem G_pos {k N : ℕ} (hN : 0 < N) : 0 < G k N := by
  apply Nat.lt_of_lt_of_le (by norm_num : 0 < 1)
  apply (le_G_iff k N 1).mpr
  intro s hs
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (hs ▸ hN)
  refine ⟨{a}, Finset.singleton_subset_iff.mpr ha, ?_, by simp⟩
  simpa only [Finset.coe_singleton] using singleton_isAPOfLengthFree a k

/-- The ratio in the question is at least one for positive $N$. -/
@[category API, AMS 5 11]
theorem one_le_ratio {N : ℕ} (hN : 0 < N) : 1 ≤ (R 3 N : ℝ) / (G 3 N : ℝ) := by
  have hG : (0 : ℝ) < G 3 N := by exact_mod_cast G_pos (k := 3) hN
  apply (le_div_iff₀ hG).mpr
  simpa using (show (G 3 N : ℝ) ≤ R 3 N from by exact_mod_cast erdos_201.variants.G_le_R 3 N)

/-- Komlós, Sulyok, and Szemerédi have shown that $R_k(N)\ll_k G_k(N)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_201.variants.comparison :
    ∀ k : ℕ, 2 ≤ k →
      (fun N : ℕ => (R k N : ℝ)) =O[atTop] (fun N : ℕ => (G k N : ℝ)) := by
  sorry

/-- $G_3(5)=3$. -/
@[category research solved, AMS 5 11]
theorem erdos_201.variants.G_three_five : G 3 5 = 3 := by
  apply le_antisymm _ three_le_G_three_five
  have hs : ({0, 1, 2, 3, 6} : Finset ℤ).card = 5 := by decide
  have hm : ({0, 1, 2, 3, 6} : Finset ℤ).maxAPFreeCard 3 = 3 := by
    rw [maxAPFreeCard_three]
    decide +kernel
  exact (G_le_maxAPFreeCard hs).trans_eq hm

/-- $R_3(5)=4$. -/
@[category research solved, AMS 5 11]
theorem erdos_201.variants.R_three_five : R 3 5 = 4 := by
  unfold R
  rw [maxAPFreeCard_three]
  decide +kernel

/-- The general guarantee can be strictly smaller than the interval extremal size. -/
@[category research solved, AMS 5 11]
theorem erdos_201.variants.strict_inequality : G 3 5 < R 3 5 := by
  rw [erdos_201.variants.G_three_five, erdos_201.variants.R_three_five]
  norm_num

/-- A finite integer set is $3$-AP-free exactly when no ordered pair starts a $3$-AP. -/
@[category API, AMS 5 11]
theorem threeAPFree_iff_pair_test (s : Finset ℤ) :
    ThreeAPFree (s : Set ℤ) ↔ ∀ a ∈ s, ∀ b ∈ s, a < b → 2 * b - a ∉ s := by
  constructor
  · intro hs a ha b hb hab hc
    have h := hs ha hb hc (by ring)
    omega
  · intro hs a ha b hb c hc habc
    by_contra hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · have heq : 2 * b - a = c := by omega
      exact hs a ha b hb hlt (heq ▸ hc)
    · have hcb : c < b := by omega
      have heq : 2 * b - c = a := by omega
      exact hs c hc b hb hcb (heq ▸ ha)

/-- $R_3(14)=8$. -/
@[category research solved, AMS 5 11]
theorem erdos_201.variants.R_three_fourteen : R 3 14 = 8 := by
  unfold R
  rw [maxAPFreeCard_three]
  apply le_antisymm
  · have hcert : ∀ t ∈ Finset.powersetCard 9 (Finset.Icc (1 : ℤ) 14),
        ¬ (∀ a ∈ t, ∀ b ∈ t, a < b → 2 * b - a ∉ t) := by
      decide +kernel
    apply Nat.le_of_lt_succ
    apply addRothNumber_lt_of_forall_not_threeAPFree
    intro t ht hf
    exact hcert t ht ((threeAPFree_iff_pair_test t).mp hf)
  · let t : Finset ℤ := {1, 2, 4, 5, 10, 11, 13, 14}
    have ht : t ⊆ Finset.Icc (1 : ℤ) 14 := by decide
    have hfree : ThreeAPFree (t : Set ℤ) := by decide +kernel
    have hcard : t.card = 8 := by decide
    exact hcard ▸ hfree.le_addRothNumber ht

/-- $G_3(14)\leq7$. -/
@[category research solved, AMS 5 11]
theorem erdos_201.variants.G_three_fourteen : G 3 14 ≤ 7 := by
  let s : Finset ℤ := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15}
  have hs : s.card = 14 := by decide
  apply (G_le_maxAPFreeCard hs).trans
  rw [maxAPFreeCard_three]
  have hcert : ∀ t ∈ Finset.powersetCard 8 s,
      ¬ (∀ a ∈ t, ∀ b ∈ t, a < b → 2 * b - a ∉ t) := by
    decide +kernel
  apply Nat.le_of_lt_succ
  apply addRothNumber_lt_of_forall_not_threeAPFree
  intro t ht hf
  exact hcert t ht ((threeAPFree_iff_pair_test t).mp hf)

/-- $G_k(N)$ is bounded above by $N$. -/
@[category API, AMS 5 11]
theorem G_le (k N : ℕ) : G k N ≤ N :=
  (erdos_201.variants.G_le_R k N).trans (R_le k N)

/-- The interval extremal size at $N=0$ is zero. -/
@[category API, AMS 5 11]
theorem R_zero (k : ℕ) : R k 0 = 0 := Nat.eq_zero_of_le_zero (R_le k 0)

/-- The general extremal size at $N=0$ is zero. -/
@[category API, AMS 5 11]
theorem G_zero (k : ℕ) : G k 0 = 0 := Nat.eq_zero_of_le_zero (G_le k 0)

/-- The known comparison has a constant depending on $k$, uniform for sufficiently large $N$. -/
@[category API, AMS 5 11]
theorem comparison_iff :
    (∀ k : ℕ, 2 ≤ k →
      (fun N : ℕ => (R k N : ℝ)) =O[atTop] (fun N : ℕ => (G k N : ℝ))) ↔
    ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, (R k N : ℝ) ≤ C * (G k N : ℝ) := by
  apply forall_congr'
  intro k
  apply imp_congr_right
  intro hk
  constructor
  · intro h
    obtain ⟨C, hC, hbound⟩ := h.exists_pos
    refine ⟨C, hC, ?_⟩
    simpa only [Real.norm_natCast] using hbound.bound
  · rintro ⟨C, hC, hbound⟩
    apply Asymptotics.IsBigO.of_bound C
    simpa only [Real.norm_natCast] using hbound

end Erdos201
