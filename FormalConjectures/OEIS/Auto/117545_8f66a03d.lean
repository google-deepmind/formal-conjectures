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

open Polynomial Int Set

/--
A117545: Least $k$ such that $\Phi(k,n)$, the $k$-th cyclotomic polynomial evaluated at $n$, is prime.
$$a(n) = \min \{k \in \mathbb{N} \mid \text{Prime}(\Phi_k(n)) \}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { k : ℕ | 0 < k ∧ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs.Prime }


theorem a_one : a 1 = 2 := by
  unfold a
  use IsLeast.csInf_eq ⟨.symm (by norm_num), fun and c=>c.1.nat_succ_le.lt_of_ne' (by norm_num ∘(.▸c.2))⟩

theorem a_two : a 2 = 2 := by
  simp_all[a]
  refine IsLeast.csInf_eq ⟨.symm (by{norm_num}), fun and true => true.1.nat_succ_le.lt_of_ne (by norm_num ∘(·▸ true.2) )⟩

theorem a_three : a 3 = 1 := by
  norm_num[a ·]
  exact IsLeast.csInf_eq ⟨.symm (by {norm_num}), fun and=> And.left⟩

theorem a_four : a 4 = 1 := by
  norm_num[a, not]
  exact IsLeast.csInf_eq ⟨.symm (by(norm_num)), fun and' => And.left⟩


/--
Note that $a(n)=1$ iff $n-1$ is prime because $\Phi(1,x)=x-1$.
-/
theorem a_n_one_iff_phi_one_n_prime (n : ℕ) :
  (a n = 1) ↔ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic 1 ℤ)).natAbs.Prime := by sorry

/--
OEIS A117545 Conjecture 0:
Is $a(n)$ defined for all $n$?
That is, for every $n \in \mathbb{N}$, does there exist a $k \in \mathbb{N}$ such that $0 < k$ and $\Phi_k(n)$ is prime?
-/
theorem a_n_is_defined_for_all_n :
  ∀ n : ℕ, ∃ k : ℕ, 0 < k ∧ (Polynomial.eval (n : ℤ) (Polynomial.cyclotomic k ℤ)).natAbs.Prime := by sorry
