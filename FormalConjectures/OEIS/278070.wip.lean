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
# Conjectures associated with a

a: $a(n) = \text{hypergeometric}([n, -n], [], -1)$.
This is equivalent to the combinatorial sum:
$$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n+k-1}{k} k!$$
The expression uses $\mathbb{N}$ arithmetic throughout, safely handling the subtraction via `Nat.pred`.

*References:*
- [A278070](https://oeis.org/A278070)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA278070

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

open Nat Finset

/--
a: $a(n) = \text{hypergeometric}([n, -n], [], -1)$.
This is equivalent to the combinatorial sum:
$$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n+k-1}{k} k!$$
The expression uses $\mathbb{N}$ arithmetic throughout, safely handling the subtraction via `Nat.pred`.
-/
def a (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    (n.choose k) * ((n + k).pred.choose k) * (k.factorial)

-- EVOLVE-BLOCK-START
-- You can put your definitions and lemmas here.
-- EVOLVE-BLOCK-END

@[category test, AMS 11]
lemma a_zero : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma a_one : a 1 = 2 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = 11 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = 106 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 1457 := by rfl


/--
a: $a(n) = \text{hypergeometric}([n, -n], [], -1)$.
This is equivalent to the combinatorial sum:
$$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n+k-1}{k} k!$$
The expression uses $\mathbb{N}$ arithmetic throughout, safely handling the subtraction via `Nat.pred`.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/278070.wip.lean#L68"]
theorem target_theorem_0
  : ∀ (n k : ℕ), Nat.ModEq k (a (n + k)) (a n) := by
  -- EVOLVE-BLOCK-START
  norm_num [ a]
  refine fun and (R) => if a : R=0 then(a)▸rfl else((( Finset.sum_nat_mod _ _ _).trans) ? _).trans (by rw [ Finset.sum_nat_mod])
  replace a x: (and+R).choose x*(and+R+x-1).choose x*x !%R=and.choose x*(and+x-1).choose x*x !%R:=add_comm and R▸R.add_choose_eq _ _▸?_
  · exact (congr_arg) (.%R) ((funext a).symm▸(Finset.sum_subset (List.range_subset.2 (by valid)) fun and A B=>by rw [Nat.choose_eq_zero_of_lt (not_lt.1 (B.comp (List.mem_range.2))), zero_mul, zero_mul, R.zero_mod]).symm)
  norm_num [mul_left_comm, add_assoc, false, Finset.sum_mul, Finset.Nat.antidiagonal_eq_map _, Finset.sum_range_succ',mul_assoc]
  refine if I : 1 ≤and+x then .trans (by rw [Nat.add_sub_assoc I, add_mul, Finset.sum_mul,mul_add, R.add_choose_eq]) ?_ else by simp_all
  norm_num[mul_left_comm, add_mul, Finset.sum_mul, Finset.mul_sum, Finset.Nat.antidiagonal_eq_map, Finset.sum_range_succ',mul_assoc]
  replace I : ∀n ∈ Finset.range x, R ∣ R.choose (n + 1)*x !:=fun a s=>match R with | S+1=>?_
  · simp_all only[mul_left_comm (R.choose (_+1)),←ZMod.val_natCast, mul_add, zero_add,push_cast,CharP.cast_eq_zero_iff _ _ _|>.2 (I _ _),ZMod.val_zero]
    hint
  · exact (.trans ⟨ _,(S.succ_mul_choose_eq _).symm⟩ ((mul_dvd_mul_left _) ((Nat.dvd_factorial (by bound) (List.mem_range.1 s)))))
  -- EVOLVE-BLOCK-END

end OeisA278070
