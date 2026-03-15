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
# Erdős Problem 1054

*Reference:* [erdosproblems.com/1054](https://www.erdosproblems.com/1054)
-/

namespace Erdos1054

open Classical Filter Asymptotics

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest
divisors of $m$ for some $k\geq 1$. -/
noncomputable def f (n : ℕ) : ℕ :=
  if h : ∃ᵉ (m) (k ≥ 1), n = ∑ i < k, Nat.nth (· ∈ m.divisors) i then
    Nat.find h
  else 0

@[category API, AMS 11]
private lemma nth_divisor_zero_eq_one {m : ℕ} (hm : m ≠ 0) :
    Nat.nth (· ∈ m.divisors) 0 = 1 := by
  rw [Nat.nth_zero]
  apply le_antisymm
  · exact Nat.sInf_le (Nat.one_mem_divisors.2 hm)
  · exact Nat.succ_le_of_lt (Nat.pos_of_mem_divisors (Nat.sInf_mem ⟨1, Nat.one_mem_divisors.2 hm⟩))

@[category API, AMS 11]
private lemma nth_divisor_one_eq_minFac {m : ℕ} (hm : m ≠ 0) (hm1 : m ≠ 1) :
    Nat.nth (· ∈ m.divisors) 1 = m.minFac := by
  let s : Set ℕ := {x | x ∈ m.divisors ∧ ∀ k < 1, Nat.nth (· ∈ m.divisors) k < x}
  have hmem : m.minFac ∈ s := by
    constructor
    · simpa [Nat.mem_divisors, hm] using And.intro (Nat.minFac_dvd m) hm
    · intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      rw [nth_divisor_zero_eq_one hm]
      exact (Nat.minFac_prime hm1).one_lt
  have hEq : Nat.nth (· ∈ m.divisors) 1 = sInf s := by
    simpa [s] using (Nat.nth_eq_sInf (fun x => x ∈ m.divisors) 1)
  apply le_antisymm
  · rw [hEq]
    exact Nat.sInf_le hmem
  · rw [hEq]
    have hsinf_mem : sInf s ∈ s := Nat.sInf_mem ⟨m.minFac, hmem⟩
    have hdiv : sInf s ∣ m := (Nat.mem_divisors.mp hsinf_mem.1).1
    have hgt0 : Nat.nth (· ∈ m.divisors) 0 < sInf s := by
      exact hsinf_mem.2 0 (by omega)
    rw [nth_divisor_zero_eq_one hm] at hgt0
    have hge2 : 2 ≤ sInf s := by omega
    exact Nat.minFac_le_of_dvd hge2 hdiv

@[category API, AMS 11]
private lemma sum_range_eq_head {g : ℕ → ℕ} {k : ℕ} (hk : 1 ≤ k)
    (hz : ∀ i, g (i + 1) = 0) :
    Finset.sum (Finset.range k) g = g 0 := by
  rcases k with _ | k
  · omega
  · rw [Finset.sum_range_succ']
    simp [hz]

@[category API, AMS 11]
private lemma sum_range_eq_first_two {g : ℕ → ℕ} {k : ℕ} (hk : 2 ≤ k)
    (hz : ∀ i, g (i + 2) = 0) :
    Finset.sum (Finset.range k) g = g 0 + g 1 := by
  rcases k with _ | k
  · omega
  rcases k with _ | k
  · omega
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp [hz, add_comm, add_left_comm]

@[category API, AMS 11]
private lemma nth_divisor_two_eq_zero_or_ge_three {m : ℕ} (hm : m ≠ 0) :
    Nat.nth (· ∈ m.divisors) 2 = 0 ∨ 3 ≤ Nat.nth (· ∈ m.divisors) 2 := by
  by_cases h2 : Nat.nth (· ∈ m.divisors) 2 = 0
  · exact Or.inl h2
  · right
    have hfinite : Set.Finite {x | x ∈ m.divisors} := m.divisors.finite_toSet
    have hcard : 2 < hfinite.toFinset.card := Nat.lt_card_toFinset_of_nth_ne_zero h2 hfinite
    have hzero : ¬ (0 ∈ m.divisors) := by simp [Nat.mem_divisors, hm]
    have h1nz : Nat.nth (· ∈ m.divisors) 1 ≠ 0 :=
      Nat.nth_ne_zero_anti hzero (by omega) h2
    have hm1 : m ≠ 1 := by
      intro hm1
      subst hm1
      simp [Nat.nth_eq_zero] at h1nz
    have h12 : Nat.nth (· ∈ m.divisors) 1 < Nat.nth (· ∈ m.divisors) 2 :=
      Nat.nth_lt_nth_of_lt_card hfinite (by omega) hcard
    rw [nth_divisor_one_eq_minFac hm hm1] at h12
    have hmf2 : 2 ≤ m.minFac := (Nat.minFac_prime hm1).two_le
    omega

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Is it true that $f(n)=o(n)$?-/
@[category research open, AMS 11]
theorem erdos_1054.parts.i : answer(sorry) ↔ (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) := by
  sorry

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Is it true that $f(n)=o(n)$ for almost all $n$? -/
@[category research open, AMS 11]
theorem erdos_1054.parts.ii : answer(sorry) ↔ ∃ (A : Set ℕ), A.HasDensity 1 ∧
    (fun (n : A) ↦ (f ↑n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) := by
  sorry

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Is it true that $\limsup f(n)/n=\infty$? -/
@[category research open, AMS 11]
theorem erdos_1054.parts.iii : answer(sorry) ↔ ∃ (A : Set ℕ), A.HasDensity 1 ∧
    atTop.limsup (fun n ↦ (f n : EReal) / n) = ⊤ := by
  sorry

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Show that $f$ is undefined at $n=2$, i.e. we get the junk value $0$. -/
@[category high_school, AMS 11]
theorem f_undefined_at_2 : f 2 = 0 := by
  unfold f
  rw [dif_neg]
  intro h
  rcases h with ⟨m, k, hk, hsum⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp at hsum
  · let g : ℕ → ℕ := fun i => Nat.nth (· ∈ m.divisors) i
    have hIio : Finset.Iio k = Finset.range k := by
      ext i
      simp
    have h0 : g 0 = 1 := nth_divisor_zero_eq_one hm
    have hsum' : 2 = Finset.sum (Finset.range k) g := by
      simpa [g, hIio] using hsum
    rcases k with _ | k
    · omega
    rcases k with _ | k
    · rw [show Finset.sum (Finset.range 1) g = g 0 by simp] at hsum'
      rw [h0] at hsum'
      norm_num at hsum'
    · by_cases h1z : g 1 = 0
      · have hzero : ¬ (0 ∈ m.divisors) := by simp [Nat.mem_divisors, hm]
        have hz : ∀ i, g (i + 1) = 0 := by
          intro i
          exact Nat.nth_eq_zero_mono hzero (Nat.succ_le_succ (Nat.zero_le i)) h1z
        have hsum1 : Finset.sum (Finset.range (k + 2)) g = 1 := by
          rw [sum_range_eq_head (by omega) hz, h0]
        rw [hsum1] at hsum'
        norm_num at hsum'
      · have hm1 : m ≠ 1 := by
          intro hm1
          subst hm1
          simp [g, Nat.nth_eq_zero] at h1z
        have h1 : g 1 = m.minFac := by
          simpa [g] using nth_divisor_one_eq_minFac hm hm1
        have hle0 : Finset.sum ({0, 1} : Finset ℕ) g ≤ Finset.sum (Finset.range (k + 2)) g := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro i hi
            simp at hi ⊢
            omega
          · intro i hi hik
            exact Nat.zero_le _
        have hle : 1 + m.minFac ≤ Finset.sum (Finset.range (k + 2)) g := by
          rw [show Finset.sum ({0, 1} : Finset ℕ) g = g 0 + g 1 by simp] at hle0
          rw [h0, h1] at hle0
          exact hle0
        rw [← hsum'] at hle
        have hmf2 : 2 ≤ m.minFac := (Nat.minFac_prime hm1).two_le
        omega

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Show that $f$ is undefined at $n=5$, i.e. we get the junk value $0$. -/
@[category high_school, AMS 11]
theorem f_undefined_at_3 : f 5 = 0 := by
  unfold f
  rw [dif_neg]
  intro h
  rcases h with ⟨m, k, hk, hsum⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp at hsum
  · let g : ℕ → ℕ := fun i => Nat.nth (· ∈ m.divisors) i
    have hIio : Finset.Iio k = Finset.range k := by
      ext i
      simp
    have h0 : g 0 = 1 := nth_divisor_zero_eq_one hm
    have hsum' : 5 = Finset.sum (Finset.range k) g := by
      simpa [g, hIio] using hsum
    rcases k with _ | k
    · omega
    rcases k with _ | k
    · rw [show Finset.sum (Finset.range 1) g = g 0 by simp] at hsum'
      rw [h0] at hsum'
      norm_num at hsum'
    · by_cases h1z : g 1 = 0
      · have hzero : ¬ (0 ∈ m.divisors) := by simp [Nat.mem_divisors, hm]
        have hz : ∀ i, g (i + 1) = 0 := by
          intro i
          exact Nat.nth_eq_zero_mono hzero (Nat.succ_le_succ (Nat.zero_le i)) h1z
        have hsum1 : Finset.sum (Finset.range (k + 2)) g = 1 := by
          rw [sum_range_eq_head (by omega) hz, h0]
        rw [hsum1] at hsum'
        norm_num at hsum'
      · have hm1 : m ≠ 1 := by
          intro hm1
          subst hm1
          simp [g, Nat.nth_eq_zero] at h1z
        have h1 : g 1 = m.minFac := by
          simpa [g] using nth_divisor_one_eq_minFac hm hm1
        rcases k with _ | k
        · have hsumRange2 : Finset.sum (Finset.range 2) g = g 0 + g 1 := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ]
            simp [g]
          rw [hsumRange2, h0, h1] at hsum'
          have hnot4 : m.minFac ≠ 4 := by
            intro h4
            have hp : Nat.Prime m.minFac := Nat.minFac_prime hm1
            norm_num [h4] at hp
          omega
        · by_cases h2z : g 2 = 0
          · have hzero : ¬ (0 ∈ m.divisors) := by simp [Nat.mem_divisors, hm]
            have hz : ∀ i, g (i + 2) = 0 := by
              intro i
              exact Nat.nth_eq_zero_mono hzero (by omega) h2z
            have hsum2 : Finset.sum (Finset.range (k + 3)) g = 1 + m.minFac := by
              rw [sum_range_eq_first_two (by omega) hz, h0, h1]
            rw [hsum2] at hsum'
            have hnot4 : m.minFac ≠ 4 := by
              intro h4
              have hp : Nat.Prime m.minFac := Nat.minFac_prime hm1
              norm_num [h4] at hp
            omega
          · have h2ge : 3 ≤ g 2 := by
              rcases nth_divisor_two_eq_zero_or_ge_three hm with h2' | h2'
              · exact False.elim (h2z h2')
              · simpa [g] using h2'
            have hle0 : Finset.sum ({0, 1, 2} : Finset ℕ) g ≤ Finset.sum (Finset.range (k + 3)) g := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro i hi
                simp at hi ⊢
                omega
              · intro i hi hik
                exact Nat.zero_le _
            have hle : 1 + m.minFac + g 2 ≤ Finset.sum (Finset.range (k + 3)) g := by
              have hs : Finset.sum ({0, 1, 2} : Finset ℕ) g = g 0 + g 1 + g 2 := by
                simp [add_assoc]
              rw [hs, h0, h1] at hle0
              exact hle0
            rw [← hsum'] at hle
            have hmf2 : 2 ≤ m.minFac := (Nat.minFac_prime hm1).two_le
            omega

end Erdos1054
