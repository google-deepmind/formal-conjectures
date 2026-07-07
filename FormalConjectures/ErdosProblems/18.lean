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
  have hdiv : Nat.divisors 6 = ({1, 2, 3, 6} : Finset ℕ) := by decide
  apply le_antisymm
  · -- practicalH 6 ≤ 2 : each m in [1,6] is a sum of at most two divisors of 6.
    apply Finset.sup_le
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hm2⟩ := hm
    interval_cases m
    · exact Nat.sInf_le ⟨{1, 2}, by rw [hdiv]; decide, by decide, {1}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 2}, by rw [hdiv]; decide, by decide, {2}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 2}, by rw [hdiv]; decide, by decide, {1, 2}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 3}, by rw [hdiv]; decide, by decide, {1, 3}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{2, 3}, by rw [hdiv]; decide, by decide, {2, 3}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 6}, by rw [hdiv]; decide, by decide, {6}, by simp, by decide⟩
  · -- 2 ≤ practicalH 6, witnessed by m = 4 (which needs two divisors: 4 = 1 + 3).
    have h4 : (4 : ℕ) ∈ Finset.Icc 1 6 := by decide
    refine le_trans ?_ (Finset.le_sup h4)
    apply le_csInf
    · exact ⟨2, {1, 3}, by rw [hdiv]; decide, by decide, {1, 3}, by simp, by decide⟩
    · rintro k ⟨D, hDsub, hDcard, B, hBsub, hBsum⟩
      by_contra hk
      push_neg at hk
      interval_cases k
      · -- D.card = 0 : D = ∅, so B = ∅ and the sum is 0 ≠ 4.
        rw [Finset.card_eq_zero] at hDcard
        subst hDcard
        rw [Finset.coe_empty, Set.subset_empty_iff, Finset.coe_eq_empty] at hBsub
        subst hBsub
        simp at hBsum
      · -- D.card = 1 : D = {d} with d ∣ 6, so the sum is 0 or d, neither equal to 4.
        rw [Finset.card_eq_one] at hDcard
        obtain ⟨d, rfl⟩ := hDcard
        have hd : d ∈ Nat.divisors 6 := hDsub (by simp)
        rw [hdiv] at hd
        rw [Finset.coe_subset, Finset.subset_singleton_iff] at hBsub
        fin_cases hd <;>
          rcases hBsub with h | h <;> subst h <;> simp at hBsum

/-- $h(12) = 3$: divisors are {1, 2, 3, 4, 6, 12}. The hardest m is
m=11, requiring 3 divisors: 11=1+4+6. -/
@[category test, AMS 11]
theorem practicalH_twelve : practicalH 12 = 3 := by
  have hdiv : Nat.divisors 12 = ({1, 2, 3, 4, 6, 12} : Finset ℕ) := by decide
  apply le_antisymm
  · -- practicalH 12 ≤ 3 : each m in [1,12] is a sum of at most three divisors of 12.
    apply Finset.sup_le
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hm2⟩ := hm
    interval_cases m
    · exact Nat.sInf_le ⟨{1, 2, 3}, by rw [hdiv]; decide, by decide, {1}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 2, 3}, by rw [hdiv]; decide, by decide, {2}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 2, 3}, by rw [hdiv]; decide, by decide, {3}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 4, 6}, by rw [hdiv]; decide, by decide, {4}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 4, 6}, by rw [hdiv]; decide, by decide, {1, 4}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 2, 3}, by rw [hdiv]; decide, by decide, {1, 2, 3}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 4, 6}, by rw [hdiv]; decide, by decide, {1, 6}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{2, 4, 6}, by rw [hdiv]; decide, by decide, {2, 6}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{3, 4, 6}, by rw [hdiv]; decide, by decide, {3, 6}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{4, 6, 12}, by rw [hdiv]; decide, by decide, {4, 6}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{1, 4, 6}, by rw [hdiv]; decide, by decide, {1, 4, 6}, by simp, by decide⟩
    · exact Nat.sInf_le ⟨{2, 4, 6}, by rw [hdiv]; decide, by decide, {2, 4, 6}, by simp, by decide⟩
  · -- 3 ≤ practicalH 12, witnessed by m = 11 (needs three divisors: 11 = 1 + 4 + 6).
    have h11 : (11 : ℕ) ∈ Finset.Icc 1 12 := by decide
    refine le_trans ?_ (Finset.le_sup h11)
    apply le_csInf
    · exact ⟨3, {1, 4, 6}, by rw [hdiv]; decide, by decide, {1, 4, 6}, by simp, by decide⟩
    · rintro k ⟨D, hDsub, hDcard, B, hBsub, hBsum⟩
      by_contra hk
      push_neg at hk
      interval_cases k
      · rw [Finset.card_eq_zero] at hDcard
        subst hDcard
        rw [Finset.coe_empty, Set.subset_empty_iff, Finset.coe_eq_empty] at hBsub
        subst hBsub
        simp at hBsum
      · rw [Finset.card_eq_one] at hDcard
        obtain ⟨d, rfl⟩ := hDcard
        have hd : d ∈ Nat.divisors 12 := hDsub (by simp)
        rw [hdiv] at hd
        rw [Finset.coe_subset, Finset.subset_singleton_iff] at hBsub
        fin_cases hd <;> rcases hBsub with h | h <;> subst h <;> simp at hBsum
      · rw [Finset.card_eq_two] at hDcard
        obtain ⟨a, b, hab, rfl⟩ := hDcard
        have ha : a ∈ Nat.divisors 12 := hDsub (by simp)
        have hb : b ∈ Nat.divisors 12 := hDsub (by simp)
        rw [hdiv] at ha hb
        have hBp : B ⊆ ({a, b} : Finset ℕ) := Finset.coe_subset.mp hBsub
        have key : ∀ S ∈ ({a, b} : Finset ℕ).powerset, S.sum (fun x => x) ≠ 11 := by
          fin_cases ha <;> fin_cases hb <;> decide
        exact key B (Finset.mem_powerset.mpr hBp) hBsum.symm

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
