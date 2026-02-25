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
# Erdős Problem 686
*Reference:* [erdosproblems.com/686](https://www.erdosproblems.com/686)
-/

namespace Erdos686

/--
Can every integer $N≥2$ be written as
$$N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research open, AMS 11]
theorem erdos_686 :
    answer(sorry) ↔ ∀ N ≥ 2, ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  sorry

/--
Can every non-square $N≥2$ be written as
$$N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research solved, AMS 11]
theorem erdos_686.variants.non_square (N : ℕ) (h_n_ge_2 : N ≥ 2) (h_not_square : ¬ ∃ s, s * s = N) : ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k), (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  exists(2),by valid
  field_simp only [ Finset.prod_Icc_succ_top,Finset.Icc_self, Finset.prod_singleton]
  by_cases h:{n|∃k,N*( (n + 1) *(n+2)) = (k + 1) *(k+2)}.Nonempty
  · obtain ⟨rfl⟩ :=h_n_ge_2.eq_or_lt
    · exact (mod_cast if a:∃ a ∈ Finset.range 30,∃n ∈ Finset.range 30,_ then a.imp fun a s=>s.2.imp fun and=>And.right else (by tauto))
    obtain ⟨A, B⟩ :=eq_or_ne N (3)
    · exact (mod_cast if a:∃ a ∈ Finset.range 30,∃n ∈ Finset.range 30,_ then a.imp fun and μ=>μ.2.imp fun and=>And.right else (by tauto))
    exact h.mono fun and=>.imp fun a s=>mod_cast (by use (by nlinarith only[pow_three and,s,show N>3by valid]))
  convert (Pell.exists_of_not_isSquare _)
  show@@_ ↔¬ IsSquare (N*4 : ℤ) →_
  · use mod_cast h.elim ∘.imp (by tauto), (. (mod_cast h_not_square ∘.rec (by use. /2,by norm_num[←., true,Nat.div_mul_div_comm _, ((2).pow_dvd_pow_iff two_ne_zero).1, false,sq])) |>.elim ↑? _)
    use fun and⟨A, B, _⟩=>absurd (eq_add_of_sub_eq B) ( A.natAbs_sq▸and.natAbs_sq▸mod_cast fun and=>(h) ? _)
    obtain ⟨l, _⟩ | ⟨a, _⟩ := ( (by ·bound : ℤ)).natAbs.even_or_odd
    · exact ( absurd (and.trans (by rw [mul_right_comm]) |>.symm.trans (by rw [ (by valid :),sq, add_mul])) (by valid ) )
    match a with|0=>field_simp[*]at and | S+1=>use A.natAbs+ S,N* A.natAbs+ S,by nlinarith only[‹_›▸and]
  omega

-- TODO: also formalize the follow-up question:
-- “If $n$ and $k$ are fixed then can one say anything about the set of integers so represented?”

end Erdos686
