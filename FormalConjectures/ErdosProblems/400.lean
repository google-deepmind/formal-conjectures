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
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp only [g]
  -- Witness: a(0) = n, a(1) = 1, a(i) = 0 for i ≥ 2
  set a : Fin (k' + 2) → ℕ := fun i =>
    if (i : ℕ) = 0 then n else if (i : ℕ) = 1 then 1 else 0 with ha_def
  have h_prod : ∏ i : Fin (k' + 2), (a i)! = n ! := by
    rw [Fin.prod_univ_succ]; simp [ha_def]
    rw [Fin.prod_univ_succ]; simp
  have h_sum : ∑ i : Fin (k' + 2), a i = n + 1 := by
    rw [Fin.sum_univ_succ]; simp [ha_def]
  -- 1 is in the set
  have hmem : 1 ∈ {(∑ i, b i) - n | (b : Fin (k' + 2) → ℕ) (_ : ∏ i, (b i)! ∣ n !)} :=
    ⟨a, h_prod ▸ dvd_refl n !, by omega⟩
  -- The set is bounded above by (k'+2) * n!
  have hbdd : BddAbove {(∑ i, b i) - n | (b : Fin (k' + 2) → ℕ) (_ : ∏ i, (b i)! ∣ n !)} := by
    refine ⟨(k' + 2) * n !, ?_⟩
    rintro x ⟨b, hb, rfl⟩
    calc (∑ i, b i) - n
        ≤ ∑ i, b i := Nat.sub_le _ _
      _ ≤ ∑ i : Fin (k' + 2), (b i)! :=
          Finset.sum_le_sum fun i _ => Nat.self_le_factorial _
      _ ≤ Finset.univ.card • n ! := by
          apply Finset.sum_le_card_nsmul; intro i _
          exact le_trans (Finset.single_le_prod' (fun j _ =>
            Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
            (Finset.mem_univ i)) (Nat.le_of_dvd (Nat.factorial_pos n) hb)
      _ = (k' + 2) * n ! := by simp [smul_eq_mul]
  exact Nat.lt_of_lt_of_le Nat.one_pos (le_csSup hbdd hmem)

end Erdos400
