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

open Nat

/--
A264025: Number of ways to write $n$ as $x^2 + y(2y+1) + \frac{z(z+1)}{2}$
where $x, y$ and $z$ are nonnegative integers with $z$ or $z+1$ prime.
-/
noncomputable def A264025 (n : ℕ) : ℕ :=
  Nat.card { p : ℕ × ℕ × ℕ //
    let (x, y, z) := p
    x ^ 2 + y * (2 * y + 1) + z * (z + 1) / 2 = n ∧
    (Nat.Prime z ∨ Nat.Prime (z + 1))
  }


theorem a_one : A264025 1 = 1 := by
  simp_all [A264025]
  refine ((congr_arg _) ((congr_arg _) ((funext @fun(x,A, B) => propext ⟨ fun and =>? _,by norm_num +contextual⟩)))).trans (Nat.card_eq_finsetCard {(0,0,1)})
  match B with|0|1=>simp_all+decide | S+2=>use absurd (add_mul S (2) (S+2 + 1)) (by (fin_omega))

theorem a_two : A264025 2 = 1 := by
  delta and A264025
  convert←Nat.card_eq_finsetCard { a ∈.range (2) ×ˢ.range (2) ×ˢ Finset.range (2)|a.1^2+a.2.1*(2*a.2.1+1)+a.2.2*(a.2.2+1)/2=2∧(a.2.2.Prime ∨(a.2.2+1).Prime)}
  simp_all
  use fun and n=>by repeat use (by nlinarith[Nat.lt_mul_div_succ (Prod.snd (Prod.snd (by assumption))*(Prod.snd (Prod.snd (by assumption)) + 1)) two_pos])

theorem a_three : A264025 3 = 1 := by
  (inhabit Int)
  simp_all[A264025]
  convert←Nat.card_eq_finsetCard { a ∈.range (2) ×ˢ.range (2) ×ˢ Finset.range (3)|a.1^2+a.2.1*(2*a.2.1+1)+a.2.2*(a.2.2+1)/2=3∧(a.2.2.Prime ∨(a.2.2+1).Prime)}
  norm_num[parity_simps,Even.two_dvd, mul_add] at*
  use fun a s=>by repeat use by nlinarith[Nat.lt_mul_div_succ (Prod.snd (Prod.snd @‹_›) *Prod.snd (Prod.snd @‹_›)+Prod.snd (Prod.snd ‹_›)) two_pos]

theorem a_four : A264025 4 = 2 := by
  delta and A264025
  convert←Nat.card_eq_finsetCard { a ∈.range (3) ×ˢ.range (3) ×ˢ.range (3)|a.1^2+a.2.1*(2*a.2.1+1)+a.2.2*(a.2.2+1)/2=4∧(a.2.2.Prime ∨(a.2.2+1).Prime)}
  revert‹_›
  exact (fun(x,A, B) => Finset.mem_filter.trans (and_iff_right_of_imp fun and=>by norm_num[show x<3∧A<3∧B<3by repeat use (by nlinarith[Nat.lt_mul_div_succ (B*(B + 1)) two_pos, and.1▸le_add_self])]))


/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344.
-/
theorem A264025_conjecture_i :
  (∀ (n : ℕ), n > 0 → A264025 n > 0) ∧
  (∀ (n : ℕ), A264025 n = 1 ↔ n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ)) := by
  sorry
