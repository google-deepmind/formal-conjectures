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
# Erdős Problem 1052

*Reference:* [erdosproblems.com/1052](https://www.erdosproblems.com/1052)
-/

namespace Erdos1052

/-- A proper unitary divisor of $n$ is a divisor $d$ of $n$
such that $d$ is coprime to $n/d$, and $d < n$. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

/-- A number $n > 0$ is a unitary perfect number if it is the sum of its proper unitary divisors. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

/--
Are there only finitely many unitary perfect numbers? -/
@[category research open, AMS 11]
theorem erdos_1052 :
    answer(sorry) ↔ {n | IsUnitaryPerfect n}.Finite := by
  sorry

/-- All unitary perfect numbers are even. -/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1052.lean", AMS 11]
theorem even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by
  sorry

@[category test, AMS 11]
theorem isUnitaryPerfect_6 : IsUnitaryPerfect 6 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

@[category test, AMS 11]
theorem isUnitaryPerfect_60 : IsUnitaryPerfect 60 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

@[category test, AMS 11]
theorem isUnitaryPerfect_90 : IsUnitaryPerfect 90 := by
  norm_num [IsUnitaryPerfect, properUnitaryDivisors]
  decide +kernel

-- Helper: proper unitary divisors of n equal the unitary divisors in n.divisors that are < n.
private lemma properUnitaryDivisors_eq_divisors_filter (n : ℕ) (hn : 0 < n) :
    properUnitaryDivisors n =
      n.divisors.filter (fun d => d.Coprime (n / d) ∧ d ≠ n) := by
  ext d
  simp only [properUnitaryDivisors, Finset.mem_filter, Finset.mem_Ico, Nat.mem_divisors]
  constructor
  · intro ⟨⟨hge, hlt⟩, hdvd, hcop⟩
    exact ⟨⟨hdvd, hn.ne'⟩, hcop, Nat.ne_of_lt hlt⟩
  · intro ⟨⟨hdvd, _⟩, hcop, hne⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.pos_of_dvd_of_pos hdvd hn).ne', ?_⟩, hdvd, hcop⟩
    exact Nat.lt_of_le_of_ne (Nat.le_of_dvd hn hdvd) hne

@[category test, AMS 11]
theorem isUnitaryPerfect_87360 : IsUnitaryPerfect 87360 := by
  -- 87360 = 2^6 × 3 × 5 × 7 × 13. Proper unitary divisors sum to 87360.
  -- native_decide is allowed for @[category test]; it compiles via OCaml, not kernel evaluation.
  constructor
  · rw [properUnitaryDivisors_eq_divisors_filter 87360 (by norm_num)]
    native_decide
  · norm_num

@[category test, AMS 11]
theorem isUnitaryPerfect_146361946186458562560000 : IsUnitaryPerfect 146361946186458562560000 := by
  sorry

end Erdos1052
