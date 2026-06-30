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
@[category textbook, AMS 11]
theorem f_undefined_at_2 : f 2 = 0 := by
  rw [f, dif_neg]
  rintro ⟨m, k, hk, hsum⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp at hsum
  · -- For `m ≠ 0` the smallest divisor is `1` and every later term is `≥ 2`, so the sum of the
    -- `k` smallest divisors is `1` or `≥ 3`, never `2`.
    have hk0 : (0 : ℕ) ∈ Finset.Iio k := Finset.mem_Iio.mpr (by omega)
    rw [← Finset.add_sum_erase _ _ hk0, Nat.nth_divisors_zero hm] at hsum
    obtain ⟨i, hi_mem, hi_ne⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (s := (Finset.Iio k).erase 0)
        (f := Nat.nth (· ∈ m.divisors)) (by omega)
    have h2 := Nat.two_le_nth_divisors hm (Finset.ne_of_mem_erase hi_mem) hi_ne
    have := h2.trans (Finset.single_le_sum (fun j _ => Nat.zero_le _) hi_mem)
    omega

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Show that $f$ is undefined at $n=5$, i.e. we get the junk value $0$. -/
@[category textbook, AMS 11]
theorem f_undefined_at_3 : f 5 = 0 := by
  rw [f, dif_neg]
  rintro ⟨m, k, hk, hsum⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp at hsum
  · set p : ℕ → Prop := fun x => x ∈ m.divisors with hpdef
    have hfin : (setOf p).Finite := Set.finite_mem_finset m.divisors
    have hg0 : Nat.nth p 0 = 1 := Nat.nth_divisors_zero hm
    -- The `j`-th smallest divisor is at least `j + 1` (for `j` below the number of divisors).
    have hlb : ∀ j, j < hfin.toFinset.card → j + 1 ≤ Nat.nth p j := by
      intro j
      induction j with
      | zero => intro _; omega
      | succ n ih =>
        intro hj
        have h1 := Nat.nth_lt_nth_of_lt_card hfin (show n < n + 1 by omega)
          (show n + 1 < hfin.toFinset.card by omega)
        have h2 := ih (by omega)
        omega
    -- The second smallest divisor of `m` is never `4`: if `4 ∣ m` then `2 ∣ m`, so `2` would be
    -- the second smallest divisor.
    have refute4 : Nat.nth p 1 ≠ 4 := by
      intro h
      have hne : Nat.nth p 1 ≠ 0 := by rw [h]; norm_num
      have hcard1 : 1 < hfin.toFinset.card := by
        by_contra hcon
        push_neg at hcon
        exact hne (Nat.nth_eq_zero.mpr (Or.inr ⟨hfin, hcon⟩))
      have hmem : p (Nat.nth p 1) := Nat.nth_mem_of_lt_card hfin hcard1
      rw [h] at hmem
      have h4 : (4 : ℕ) ∣ m := (Nat.mem_divisors.mp hmem).1
      have h2d : (2 : ℕ) ∣ m := dvd_trans (by norm_num) h4
      have h2mem : p 2 := by simp [hpdef, Nat.mem_divisors, h2d, hm]
      have hcount : Nat.count p 2 = 1 := by
        simp [hpdef, Nat.count_succ, Nat.count_zero, Nat.mem_divisors, hm]
      have hnc := Nat.nth_count (p := p) h2mem
      rw [hcount, h] at hnc
      norm_num at hnc
    rcases lt_or_ge k 3 with hk3 | hk3
    · -- `k = 1` or `k = 2`.
      interval_cases k
      · rw [Nat.Iio_eq_range, Finset.sum_range_one, hg0] at hsum
        omega
      · rw [Nat.Iio_eq_range, Finset.sum_range_succ, Finset.sum_range_one, hg0] at hsum
        exact refute4 (by omega)
    · -- `k ≥ 3`.
      rcases eq_or_ne (Nat.nth p 2) 0 with hg2 | hg2
      · -- At most two divisors are involved, so the sum equals `1 + Nat.nth p 1`.
        have hz : ∀ i, 2 ≤ i → Nat.nth p i = 0 := by
          rcases Nat.nth_eq_zero.mp hg2 with ⟨hp0', _⟩ | ⟨hf, hcle⟩
          · exact absurd hp0' (by simp [hpdef, Nat.mem_divisors])
          · intro i hi
            refine Nat.nth_eq_zero.mpr (Or.inr ⟨hfin, ?_⟩)
            have heq : hf.toFinset.card = hfin.toFinset.card := by congr 1
            omega
        rw [← Finset.sum_subset (s₁ := Finset.Iio 2) (s₂ := Finset.Iio k)] at hsum
        · rw [Nat.Iio_eq_range, Finset.sum_range_succ, Finset.sum_range_one, hg0] at hsum
          exact refute4 (by omega)
        · intro x hx; simp only [Finset.mem_Iio] at *; omega
        · intro x hx hx2; simp only [Finset.mem_Iio] at *; exact hz x (by omega)
      · -- Three distinct divisors `1 < d₁ < d₂` force the sum to be at least `6`.
        have hc3 : 2 < hfin.toFinset.card := by
          by_contra hcon
          push_neg at hcon
          exact hg2 (Nat.nth_eq_zero.mpr (Or.inr ⟨hfin, hcon⟩))
        have hg1 := hlb 1 (by omega)
        have hg2' := hlb 2 (by omega)
        have hsub : ∑ i ∈ Finset.Iio 3, Nat.nth p i ≤ ∑ i ∈ Finset.Iio k, Nat.nth p i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx; simp only [Finset.mem_Iio] at *; omega
          · intros; positivity
        rw [Nat.Iio_eq_range, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_one, hg0] at hsub
        rw [Nat.Iio_eq_range] at hsum
        omega

end Erdos1054
