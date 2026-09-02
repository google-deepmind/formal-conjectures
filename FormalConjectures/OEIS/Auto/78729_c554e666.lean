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

open Nat Finset Set

/--
The product $(k+1)(k+2)\cdots(k+n)$.
-/
def A078729_product (n k : ℕ) : ℕ :=
  (Finset.range n).prod (fun i ↦ k + i + 1)

/--
A078729: $a(n)$ is the least positive integer $k$ such that
$$(k+1)(k+2)\cdots(k+n) + 1$$
is prime, if such $k$ exists; otherwise, $a(n) = 0$.
-/
noncomputable def A078729 (n : ℕ) : ℕ :=
  sInf { k : ℕ | k > 0 ∧ (A078729_product n k + 1).Prime }


theorem a_one : A078729 1 = 1 := by
  push_cast[ A078729]
  refine IsLeast.csInf_eq ⟨.symm (by norm_num [A078729_product]), fun and' => And.left⟩

theorem a_two : A078729 2 = 1 := by
  delta and A078729
  refine IsLeast.csInf_eq ⟨.symm (by·norm_num[A078729_product]), fun and=>And.left⟩

theorem a_three : A078729 3 = 2 := by
  push_cast [ A078729]
  exact IsLeast.csInf_eq ⟨ And.symm (by norm_num [A078729_product]), fun and true => true.1.nat_succ_le.lt_of_ne' ↑(mt (@ ·▸ true.2) (by norm_num[A078729_product]))⟩

theorem a_four : A078729 4 = 0 := by
  delta and A078729
  norm_num[Iff, A078729_product]
  norm_num[ Finset.prod_range_succ]
  exact (bot_unique fun and true => true.2.eq_one_or_self_of_dvd (@ (and+4) * (and+1) + 1) ⟨ (and+4) * ( and+1) +1,by ·ring⟩ |>.elim ↑nofun fun and' =>by (nlinarith![pow_three and]))


/--
Conjecture: $a(n) = 0$ if and only if $n=4$.
-/
theorem oeis_78729_conjecture_0 : ∀ n : ℕ, A078729 n = 0 ↔ n = 4 := by sorry
