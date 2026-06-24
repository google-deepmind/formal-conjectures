/-
Copyright 2026 Google LLC

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

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option maxHeartbeats 200000




open Nat Finset

/--
A278070: $a(n) = \text{hypergeometric}([n, -n], [], -1)$.
This is equivalent to the combinatorial sum:
$$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n+k-1}{k} k!$$
The expression uses $\mathbb{N}$ arithmetic throughout, safely handling the subtraction via `Nat.pred`.
-/
def A278070 (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    (n.choose k) * ((n + k).pred.choose k) * (k.factorial)

open MeasureTheory

open Polynomial

open scoped BigOperators

open scoped Classical

open scoped ENNReal

open scoped EuclideanGeometry

open scoped InnerProductSpace

open scoped intervalIntegral

open scoped List

open scoped Matrix

open scoped Nat

open scoped NNReal

open scoped Pointwise

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START
-- You can put your definitions and lemmas here.
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : ∀ (n k : ℕ), Nat.ModEq k (A278070 (n + k)) (A278070 n) := by
  -- EVOLVE-BLOCK-START
  norm_num [ A278070]
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
