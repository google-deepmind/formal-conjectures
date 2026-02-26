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
# Erdős Problem 400

*Reference:* [erdosproblems.com/400](https://www.erdosproblems.com/400)
-/

open Nat Filter Finset
open scoped Asymptotics Topology

namespace Erdos400

/--
For any $k\geq 2$ let $g_k(n)$ denote the maximum value of $(a_1+\cdots+a_k)-n$
where $a_1,\ldots,a_k$ are integers such that $a_1!\cdots a_k! \mid n!$.
-/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup { ((∑ i, a i) - n) | (a : Fin k → ℕ) (_ : (∏ i, (a i) !) ∣ n !) }

/--
Can one show that $\sum_{n\leq x}g_k(n) \sim c_k x\log x$ for some constant $c_k$?
-/
@[category research open, AMS 11]
theorem erdos_400.parts.i :
    answer(sorry) ↔ ∀ᵉ (k ≥ 2), ∃ c : ℝ,
      (fun x : ℕ ↦ (∑ n ∈ Icc 1 x, (g k n : ℝ))) ~[atTop]
      (fun x : ℕ ↦ c * x * Real.log x) := by
  sorry

/--
Is it true that there is a constant $c_k$ such that for almost all $n < x$ we have
$g_k(n)=c_k\log x+o(\log x)$?
-/
@[category research open, AMS 11]
theorem erdos_400.parts.ii :
    answer(sorry) ↔ ∀ᵉ (k ≥ 2), ∃ c : ℝ, ∀ ε > 0,
      Tendsto (fun x : ℕ ↦
        (((Icc 1 x).filter (fun n ↦
          |(g k n : ℝ) - c * Real.log x| ≤ ε * Real.log x)).card : ℝ) / x)
        atTop (𝓝 1) := by
  sorry

/--
Erdős and Graham write that it is easy to show that $g_k(n) \ll_k \log n$ always, but the best
possible constant is unknown.
-/
@[category research solved, AMS 11]
theorem erdos_400.variants.upper_bound (k : ℕ) (hk : k ≥ 2) :
    (fun n : ℕ ↦ (g k n : ℝ)) ≪ (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  sorry


/-- For $k \ge 2$, $g_k(n) > 0$. We show this by choosing $a = (n, 1, 0, \ldots, 0)$. -/
@[category test, AMS 11]
theorem erdos_400.variants.g_pos (k n : ℕ) (h: k ≥ 2) : 0 < g k n := by
  have hz : 0 < k := by omega
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  let a : Fin k → ℕ := fun i ↦
    if i = ⟨0, h0⟩ then n else if i = ⟨1, h1⟩ then 1 else 0
  have h1_ne_0 : (⟨1, h1⟩ : Fin k) ≠ ⟨0, h0⟩ := by
    intro hc
    apply Nat.zero_ne_one
    exact (Fin.mk.inj hc).symm
  have h_prod : (∏ i, (a i) !) ∣ n ! := by
    have : (∏ i, (a i) !) = n ! := by
      calc
        (∏ i, (a i) !) = (a ⟨0, h0⟩) ! := by
          refine Fintype.prod_eq_single (⟨0, h0⟩ : Fin k) ?_
          intro i hi0
          dsimp [a]
          split_ifs with h_1
          · exact (hi0 h_1).elim
          · rfl
          · rfl
        _ = n ! := by simp [a]
    exact dvd_of_eq this
  have h_sum : (∑ i, a i) - n = 1 := by
    have ha_eq : a = fun i ↦ (if i = ⟨0, h0⟩ then n else 0) + (if i = ⟨1, h1⟩ then 1 else 0) := by
      ext i
      dsimp [a]
      split_ifs with h_1 h_2
      · subst h_1; exfalso; exact h1_ne_0 h_2.symm
      · rfl
      · rfl
      · rfl
    rw [ha_eq, Finset.sum_add_distrib]
    simp
  have h_mem : 1 ∈ { ((∑ i, a i) - n) | (a : Fin k → ℕ) (_ : (∏ i, (a i) !) ∣ n !) } := by
    simp only [Set.mem_setOf_eq]
    exact ⟨a, h_prod, h_sum⟩
  have h_le : 1 ≤ g k n := by
    have h_bdd : BddAbove { ((∑ i, a i) - n) | (a : Fin k → ℕ) (_ : (∏ i, (a i) !) ∣ n !) } := by
      use (k * n !)
      rintro x ⟨a', h_div, rfl⟩
      have h_le_fa : ∀ i, a' i ≤ (a' i) ! := by
        intro i
        cases (a' i) with
        | zero => exact Nat.zero_le 1
        | succ m =>
          have hm : 1 ≤ m ! := Nat.factorial_pos m
          calc
            m + 1 = (m + 1) * 1 := by ring
            _ ≤ (m + 1) * m ! := Nat.mul_le_mul_left _ hm
            _ = (m + 1) ! := rfl
      have h_le_n : ∀ i, (a' i) ! ≤ n ! := by
        intro i
        have hd1 : (a' i) ! ∣ ∏ j, (a' j) ! := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
        have hd2 : (a' i) ! ∣ n ! := dvd_trans hd1 h_div
        exact Nat.le_of_dvd (Nat.factorial_pos n) hd2
      have h_a_le : ∀ i, a' i ≤ n ! := fun i => le_trans (h_le_fa i) (h_le_n i)
      have h_sum_le : (∑ i, a' i) ≤ k * n ! := by
        have hs : (∑ i : Fin k, n !) = k * n ! := by simp
        rw [← hs]
        exact Finset.sum_le_sum fun i _ => h_a_le i
      omega
    exact le_csSup h_bdd h_mem
  exact h_le

end Erdos400
