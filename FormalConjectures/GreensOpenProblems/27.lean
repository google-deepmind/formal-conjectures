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

import FormalConjecturesUtil

/-!
# Green's Open Problem 27

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.27)
- [Be23] Bedert, Benjamin. "On unique sums in Abelian groups." Combinatorica 44.2 (2024): 269-298.
- [St76] Straus, E. G. "Differences of residues (mod p)." Journal of Number Theory 8.1 (1976): 40-42.
- [A398173] [OEIS A398173](https://oeis.org/A398173), the values of $m(p)$ for the first primes.
-/

open Asymptotics Filter

namespace Green27

/--
This is $m(p)$ in [Be23]: the size of the smallest set $A \subset \mathbb{Z} / p\mathbb{Z}$ (with
at least two elements) for which no element in the sumset $A + A$ has a unique representation.
-/
noncomputable def m (p : ℕ) : ℝ :=
  (sInf { (A.card) | (A : Finset (ZMod p)) (_ : 2 ≤ A.card) (_ : HasNoUniqueRepresentation A) } : ℝ)

/-- `atTop` restricted to prime numbers. -/
def primesAtTop : Filter ℕ := atTop ⊓ 𝓟 {p : ℕ | p.Prime}

/-- Best-known lower bound [Be23, Theorem 3]. -/
noncomputable def lowerBest (p : ℕ) : ℝ :=
  (Real.sqrt (Real.log (Real.log (Real.log (p : ℝ)))) /
   Real.log (Real.log (Real.log (Real.log (p : ℝ))))) * Real.log (p : ℝ)

/-- Best-known upper bound [Be23, Theorem 5]. -/
noncomputable def upperBest (p : ℕ) : ℝ := (Real.log (p : ℝ)) ^ 2

/--
What is the size of the smallest set $A \subset \mathbb{Z} / p\mathbb{Z}$ (with at least two elements)
for which no element in the sumset $A + A$ has a unique representation?
-/
@[category research open, AMS 5 11]
theorem green_27.equivalent :
  (answer(sorry) : ℕ → ℝ) ~[primesAtTop] m := by
  sorry

/-- Propose a better lower bound along primes. -/
@[category research open, AMS 5 11]
theorem green_27.lower :
    let ans := (answer(sorry) : ℕ → ℝ)
    (lowerBest =o[primesAtTop] ans) ∧ (ans =O[primesAtTop] m) := by
  sorry

/-- Propose a better upper bound along primes. -/
@[category research open, AMS 5 11]
theorem green_27.upper :
    let ans := (answer(sorry) : ℕ → ℝ)
    (ans =o[primesAtTop] upperBest) ∧ (m =O[primesAtTop] ans) := by
  sorry

/--
We have $m(p) \geq \omega(p) \log p$ for some function $\omega(p)$ tending to infinity [Be23, Theorem 3].
-/
@[category research solved, AMS 5 11]
theorem green_27.variants.lower_be23 :
  ∃ ω : ℕ → ℝ, Tendsto ω primesAtTop atTop ∧
    ∀ᶠ p in primesAtTop,
      ω p * Real.log (p : ℝ) ≤ m p := by
  sorry

/-- Upper bound: $m(p) \ll (\log p)^2$ [Be23, Theorem 5]. -/
@[category research solved, AMS 5 11]
theorem green_27.variants.upper_be23 :
  m =O[primesAtTop] upperBest := by
  sorry

/-- Previous best-known lower bound $\log p \ll m(p)$ from [St76]. -/
@[category research solved, AMS 5 11]
theorem green_27.variants.previous_lower :
  (fun p ↦ Real.log (p : ℝ)) =O[primesAtTop] m := by
  sorry

/-- Previous best-known upper bound $m(p) \ll \sqrt{p}$ from [Be23]. -/
@[category research solved, AMS 5 11]
theorem green_27.variants.previous_upper :
  m =O[primesAtTop] (fun p ↦ Real.sqrt (p : ℝ)) := by
  sorry

/-
### Values at small primes

The statements above are asymptotic. The declarations below pin `m` down at concrete primes,
against the values recorded in [A398173]. Every proof is a finite computation checked by the
kernel.

For `p = 3, 5, 7` the whole subset lattice of `ZMod p` is small enough to decide, so these are
exact values: both `m p ≤ k` and `k ≤ m p`. They fix the reading of the definition in both
directions, which an upper bound alone would not do.

For the six larger primes only the upper bound is given. The matching lower bounds come from an
exhaustive search over subsets of `ZMod p` that is far out of reach of a kernel computation; they
are established elsewhere and are not formalised in this repository.
-/

/-- An explicit `3`-element subset of `ZMod 3` in which no element of `A + A` has a unique
representation. -/
def witness3 : Finset (ZMod 3) := {0, 1, 2}

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- $m(3) = 3$, by exhibiting a set of size `3` and checking that no smaller set works. -/
@[category test, AMS 5 11]
theorem m_3_eq : m 3 = 3 := by
  have key : ∀ A : Finset (ZMod 3), 2 ≤ A.card → HasNoUniqueRepresentation A → 3 ≤ A.card := by
    simp only [HasNoUniqueRepresentation, allUniqueSums, Set.eq_empty_iff_forall_notMem,
      Set.mem_ofPred_eq, Finset.mem_coe, not_exists, not_and]
    decide
  have hw : HasNoUniqueRepresentation witness3 := by
    rw [HasNoUniqueRepresentation, Set.eq_empty_iff_forall_notMem]
    simp only [allUniqueSums, Set.mem_ofPred_eq, Finset.mem_coe, not_exists, not_and]
    decide
  have hcard : witness3.card = 3 := by decide
  apply le_antisymm
  · exact csInf_le ⟨0, by rintro x ⟨A, -, -, rfl⟩; positivity⟩
      ⟨witness3, by decide, hw, by norm_num [hcard]⟩
  · refine le_csInf ⟨_, witness3, by decide, hw, rfl⟩ ?_
    rintro x ⟨A, hA2, hA, rfl⟩
    exact_mod_cast key A hA2 hA

/-- An explicit `4`-element subset of `ZMod 5` in which no element of `A + A` has a unique
representation. -/
def witness5 : Finset (ZMod 5) := {0, 1, 2, 3}

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- $m(5) = 4$, by exhibiting a set of size `4` and checking that no smaller set works. -/
@[category test, AMS 5 11]
theorem m_5_eq : m 5 = 4 := by
  have key : ∀ A : Finset (ZMod 5), 2 ≤ A.card → HasNoUniqueRepresentation A → 4 ≤ A.card := by
    simp only [HasNoUniqueRepresentation, allUniqueSums, Set.eq_empty_iff_forall_notMem,
      Set.mem_ofPred_eq, Finset.mem_coe, not_exists, not_and]
    decide
  have hw : HasNoUniqueRepresentation witness5 := by
    rw [HasNoUniqueRepresentation, Set.eq_empty_iff_forall_notMem]
    simp only [allUniqueSums, Set.mem_ofPred_eq, Finset.mem_coe, not_exists, not_and]
    decide
  have hcard : witness5.card = 4 := by decide
  apply le_antisymm
  · exact csInf_le ⟨0, by rintro x ⟨A, -, -, rfl⟩; positivity⟩
      ⟨witness5, by decide, hw, by norm_num [hcard]⟩
  · refine le_csInf ⟨_, witness5, by decide, hw, rfl⟩ ?_
    rintro x ⟨A, hA2, hA, rfl⟩
    exact_mod_cast key A hA2 hA

/-- An explicit `5`-element subset of `ZMod 7` in which no element of `A + A` has a unique
representation. -/
def witness7 : Finset (ZMod 7) := {0, 1, 2, 3, 4}

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- $m(7) = 5$, by exhibiting a set of size `5` and checking that no smaller set works. -/
@[category test, AMS 5 11]
theorem m_7_eq : m 7 = 5 := by
  have key : ∀ A : Finset (ZMod 7), 2 ≤ A.card → HasNoUniqueRepresentation A → 5 ≤ A.card := by
    simp only [HasNoUniqueRepresentation, allUniqueSums, Set.eq_empty_iff_forall_notMem,
      Set.mem_ofPred_eq, Finset.mem_coe, not_exists, not_and]
    decide
  have hw : HasNoUniqueRepresentation witness7 := by
    rw [HasNoUniqueRepresentation, Set.eq_empty_iff_forall_notMem]
    simp only [allUniqueSums, Set.mem_ofPred_eq, Finset.mem_coe, not_exists, not_and]
    decide
  have hcard : witness7.card = 5 := by decide
  apply le_antisymm
  · exact csInf_le ⟨0, by rintro x ⟨A, -, -, rfl⟩; positivity⟩
      ⟨witness7, by decide, hw, by norm_num [hcard]⟩
  · refine le_csInf ⟨_, witness7, by decide, hw, rfl⟩ ?_
    rintro x ⟨A, hA2, hA, rfl⟩
    exact_mod_cast key A hA2 hA

/-- An explicit `14`-element subset of `ZMod 53` in which no element of `A + A` has a unique
representation. -/
def witness53 : Finset (ZMod 53) := {0, 1, 5, 7, 14, 16, 18, 28, 32, 35, 36, 39, 43, 51}

@[category test, AMS 5 11]
theorem witness53_card : witness53.card = 14 := by decide

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[category test, AMS 5 11]
theorem witness53_hasNoUniqueRepresentation : HasNoUniqueRepresentation witness53 := by
  rw [HasNoUniqueRepresentation, Set.eq_empty_iff_forall_notMem]
  simp only [allUniqueSums, Set.mem_ofPred_eq, Finset.mem_coe, not_exists, not_and]
  decide

/-- `witness53` gives $m(53) \leq 14$. -/
@[category test, AMS 5 11]
theorem m_53_le_fourteen : m 53 ≤ 14 := by
  apply csInf_le
  · exact ⟨0, by rintro x ⟨A, -, -, rfl⟩; positivity⟩
  · exact ⟨witness53, by decide, witness53_hasNoUniqueRepresentation, by
      norm_num [witness53_card]⟩

/-- An explicit `15`-element subset of `ZMod 59` in which no element of `A + A` has a unique
representation. -/
def witness59 : Finset (ZMod 59) := {0, 1, 2, 3, 4, 5, 9, 10, 16, 25, 27, 32, 42, 44, 48}

@[category test, AMS 5 11]
theorem witness59_card : witness59.card = 15 := by decide

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[category test, AMS 5 11]
theorem witness59_hasNoUniqueRepresentation : HasNoUniqueRepresentation witness59 := by
  rw [HasNoUniqueRepresentation, Set.eq_empty_iff_forall_notMem]
  simp only [allUniqueSums, Set.mem_ofPred_eq, Finset.mem_coe, not_exists, not_and]
  decide

/-- `witness59` gives $m(59) \leq 15$. -/
@[category test, AMS 5 11]
theorem m_59_le_fifteen : m 59 ≤ 15 := by
  apply csInf_le
  · exact ⟨0, by rintro x ⟨A, -, -, rfl⟩; positivity⟩
  · exact ⟨witness59, by decide, witness59_hasNoUniqueRepresentation, by
      norm_num [witness59_card]⟩

/-- An explicit `15`-element subset of `ZMod 61` in which no element of `A + A` has a unique
representation. -/
def witness61 : Finset (ZMod 61) := {0, 1, 2, 3, 4, 6, 15, 21, 22, 24, 42, 49, 55, 56, 58}

@[category test, AMS 5 11]
theorem witness61_card : witness61.card = 15 := by decide

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[category test, AMS 5 11]
theorem witness61_hasNoUniqueRepresentation : HasNoUniqueRepresentation witness61 := by
  rw [HasNoUniqueRepresentation, Set.eq_empty_iff_forall_notMem]
  simp only [allUniqueSums, Set.mem_ofPred_eq, Finset.mem_coe, not_exists, not_and]
  decide

/-- `witness61` gives $m(61) \leq 15$. -/
@[category test, AMS 5 11]
theorem m_61_le_fifteen : m 61 ≤ 15 := by
  apply csInf_le
  · exact ⟨0, by rintro x ⟨A, -, -, rfl⟩; positivity⟩
  · exact ⟨witness61, by decide, witness61_hasNoUniqueRepresentation, by
      norm_num [witness61_card]⟩

/-- An explicit `16`-element subset of `ZMod 67` in which no element of `A + A` has a unique
representation. -/
def witness67 : Finset (ZMod 67) := {0, 1, 2, 3, 4, 5, 6, 7, 11, 14, 15, 25, 26, 50, 53, 54}

@[category test, AMS 5 11]
theorem witness67_card : witness67.card = 16 := by decide

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[category test, AMS 5 11]
theorem witness67_hasNoUniqueRepresentation : HasNoUniqueRepresentation witness67 := by
  rw [HasNoUniqueRepresentation, Set.eq_empty_iff_forall_notMem]
  simp only [allUniqueSums, Set.mem_ofPred_eq, Finset.mem_coe, not_exists, not_and]
  decide

/-- `witness67` gives $m(67) \leq 16$. -/
@[category test, AMS 5 11]
theorem m_67_le_sixteen : m 67 ≤ 16 := by
  apply csInf_le
  · exact ⟨0, by rintro x ⟨A, -, -, rfl⟩; positivity⟩
  · exact ⟨witness67, by decide, witness67_hasNoUniqueRepresentation, by
      norm_num [witness67_card]⟩

/-- An explicit `16`-element subset of `ZMod 71` in which no element of `A + A` has a unique
representation. -/
def witness71 : Finset (ZMod 71) := {0, 1, 2, 3, 4, 5, 7, 8, 12, 31, 45, 46, 57, 59, 61, 64}

@[category test, AMS 5 11]
theorem witness71_card : witness71.card = 16 := by decide

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[category test, AMS 5 11]
theorem witness71_hasNoUniqueRepresentation : HasNoUniqueRepresentation witness71 := by
  rw [HasNoUniqueRepresentation, Set.eq_empty_iff_forall_notMem]
  simp only [allUniqueSums, Set.mem_ofPred_eq, Finset.mem_coe, not_exists, not_and]
  decide

/-- `witness71` gives $m(71) \leq 16$. -/
@[category test, AMS 5 11]
theorem m_71_le_sixteen : m 71 ≤ 16 := by
  apply csInf_le
  · exact ⟨0, by rintro x ⟨A, -, -, rfl⟩; positivity⟩
  · exact ⟨witness71, by decide, witness71_hasNoUniqueRepresentation, by
      norm_num [witness71_card]⟩

/-- An explicit `16`-element subset of `ZMod 73` in which no element of `A + A` has a unique
representation. -/
def witness73 : Finset (ZMod 73) := {0, 1, 2, 3, 4, 5, 8, 9, 13, 21, 23, 25, 29, 44, 45, 65}

@[category test, AMS 5 11]
theorem witness73_card : witness73.card = 16 := by decide

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[category test, AMS 5 11]
theorem witness73_hasNoUniqueRepresentation : HasNoUniqueRepresentation witness73 := by
  rw [HasNoUniqueRepresentation, Set.eq_empty_iff_forall_notMem]
  simp only [allUniqueSums, Set.mem_ofPred_eq, Finset.mem_coe, not_exists, not_and]
  decide

/-- `witness73` gives $m(73) \leq 16$. -/
@[category test, AMS 5 11]
theorem m_73_le_sixteen : m 73 ≤ 16 := by
  apply csInf_le
  · exact ⟨0, by rintro x ⟨A, -, -, rfl⟩; positivity⟩
  · exact ⟨witness73, by decide, witness73_hasNoUniqueRepresentation, by
      norm_num [witness73_card]⟩

end Green27
