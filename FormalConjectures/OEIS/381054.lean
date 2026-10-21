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

module

public import FormalConjecturesUtil

/-!
# Square-root gaps of closest factor pairs

For each positive integer $m$, the family associated with A381054 chooses the least positive
multiplier $k$ such that the integer square roots of the closest factor pair of $nk$ differ
by $m$. The original sequence is the member $m=1$.

*References:*
- [OEIS A381054](https://oeis.org/A381054)
- [J. J. Gebendorfer, A boundary counterexample to the general-family comment]
  (https://github.com/RhudeJJJJ/formal-conjectures/blob/d8348148865175409dc83ac241ce342f43d395c3/Papers/20261021/baloui.tex)
-/

@[expose] public section

namespace OeisA381054

/-- The largest positive divisor not exceeding the integer square root. -/
def smallDivisor (q : ℕ) : ℕ :=
  ((Finset.range (Nat.sqrt q + 1)).filter fun d => 0 < d ∧ d ∣ q).sup id

/-- Difference of the integer square roots of the closest factor pair. -/
def gap (q : ℕ) : ℤ :=
  (Nat.sqrt (q / smallDivisor q) : ℤ) - (Nat.sqrt (smallDivisor q) : ℤ)

/-- Admissible positive multipliers in the general family. -/
def Admissible (m n k : ℕ) : Prop := 0 < k ∧ gap (n * k) = (m : ℤ)

instance (m n k : ℕ) : Decidable (Admissible m n k) :=
  inferInstanceAs (Decidable (0 < k ∧ gap (n * k) = (m : ℤ)))

/-- Least positive admissible multiplier, with value zero if none exists. -/
noncomputable def aFamily (m n : ℕ) : ℕ := sInf {k | Admissible m n k}

private theorem a_family_eq (m n k : ℕ) (hk : Admissible m n k)
    (hsmall : ∀ j ∈ Finset.range k, ¬ Admissible m n j) : aFamily m n = k := by
  apply IsLeast.csInf_eq
  refine ⟨hk, ?_⟩
  intro j hj
  by_contra! h
  exact hsmall j (Finset.mem_range.mpr h) hj

/-- The sequence A381054 itself is the member with gap one. -/
noncomputable def a (n : ℕ) : ℕ := aFamily 1 n

@[category test, AMS 11]
theorem a_1 : a 1 = 5 := a_family_eq 1 1 5 (by decide +kernel) (by decide +kernel)
@[category test, AMS 11]
theorem a_2 : a 2 = 4 := a_family_eq 1 2 4 (by decide +kernel) (by decide +kernel)
@[category test, AMS 11]
theorem a_3 : a 3 = 4 := a_family_eq 1 3 4 (by decide +kernel) (by decide +kernel)
@[category test, AMS 11]
theorem a_4 : a 4 = 2 := a_family_eq 1 4 2 (by decide +kernel) (by decide +kernel)
@[category test, AMS 11]
theorem a_5 : a 5 = 1 := a_family_eq 1 5 1 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The least positive multiplier with gap three at $n=11$ is $37$. -/
@[category test, AMS 11]
theorem a_family_3_11 : aFamily 3 11 = 37 :=
  a_family_eq 3 11 37 (by decide +kernel) (by decide +kernel)

/-- The general-family comment, restricted to inputs where the minimum exists.
The square uses integer subtraction, including when the proposed value is zero. -/
def FamilyConjecture : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → (∃ k, Admissible m n k) →
    ((aFamily m n : ℤ) = ((Nat.sqrt n : ℤ) - (m : ℤ)) ^ 2 ↔
      n.Prime ∧ m ^ 2 + 1 < n)

/--
The OEIS general-family comment conjectures
"$a_m(n)=(A000196(n)-m)^2$ iff $n$ is a prime $>m^2+1$".
The assertion is false at $m=3$, $n=11$, where the minimum exists and is $37$.
This refutes even the restriction to inputs where the minimum exists.

Written proof by Jonas J. Gebendorfer; Lean formalization assisted by OpenAI Codex.
-/
@[category research solved, question, AMS 11]
theorem not_family_conjecture : ¬ FamilyConjecture := by
  intro h
  have heq := (h 3 11 (by decide +kernel) (by decide +kernel) ⟨37, by decide +kernel⟩).mpr (by decide +kernel)
  rw [a_family_3_11] at heq
  norm_num [show Nat.sqrt 11 = 3 from by decide +kernel] at heq

end OeisA381054
