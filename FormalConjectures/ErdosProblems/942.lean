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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 942

*Reference:* [erdosproblems.com/942](https://www.erdosproblems.com/942)
-/

@[expose] public section

open Nat Filter Topology

namespace Erdos942

/--
Let $h(n)$ count the number of powerful integers in $[n^2, (n + 1)^2)$.
-/
def erdos_942.h (n : ℕ) : ℕ := ((Finset.Ico (n ^ 2) ((n + 1) ^ 2)).filter Powerful).card

/--
Is there some constant $c > 0$ such that $h(n) < (\log n)^{c + o(1)}$ and, for infinitely many $n$,
$h(n) > (\log n)^{c - o(1)}$.
-/
@[category research open, question, AMS 11]
theorem erdos_942 : ∃ c > 0, ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    (∀ᶠ n in atTop, erdos_942.h n < (Real.log n) ^ (c + o n)) ∧
    {n | erdos_942.h n > (Real.log n) ^ (c - o n)}.Infinite := by
  sorry

/--
It is not hard to prove that $\limsup h(n) = \infty$.
-/
@[category textbook, AMS 11]
theorem erdos_942.variants.limsup :
    atTop.limsup (((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942.h)) = ⊤ := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  refine iInf_eq_top.mpr fun N => ENat.eq_top_iff_forall_ge.mpr fun k => ?_
  have hle : ∀ n, erdos_942.h n ≤ 2 * n + 1 := fun n => by
    unfold erdos_942.h
    calc _ ≤ (Finset.Ico (n ^ 2) ((n + 1) ^ 2)).card := Finset.card_filter_le _ _
      _ = 2 * n + 1 := by simp; ring_nf; omega
  obtain ⟨q, hq, hK⟩ := Nat.exists_card_powerful_near_sq_ge (2 * (k + 2 * N + 2))
  obtain ⟨n, hn⟩ : ∃ n, k + 2 * N + 2 ≤ erdos_942.h n := by
    by_cases h : k + 2 * N + 2 ≤ erdos_942.h q
    · exact ⟨q, h⟩
    · refine ⟨q - 1, ?_⟩
      unfold erdos_942.h at h ⊢
      rw [show q - 1 + 1 = q by omega]
      omega
  have hNn : N ≤ n := by have := hle n; omega
  refine le_iSup₂_of_le n hNn ?_
  simp only [Function.comp_apply]
  exact_mod_cast (show k ≤ erdos_942.h n by omega)

/--
It is not hard to prove that the density $\delta_l$ of integers for which $h(n) = l$ exists
and satisfies $$\sum_l \delta_l = 1$$.
-/
@[category textbook, AMS 11]
theorem erdos_942.variants.density :
    ∃ δ : ℕ → ℝ, ∀ l, {n | erdos_942.h n = l}.HasDensity (δ l) ∧
    ∑' l, δ l = 1 := by
  sorry

end Erdos942
