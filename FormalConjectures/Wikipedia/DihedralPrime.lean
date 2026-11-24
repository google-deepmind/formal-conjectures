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
# Infinitude of Dihedral Primes

A base-$10$ prime $p$ is *dihedral* (or a *dihedral calculator prime*,
[OEIS A134996](https://oeis.org/A134996)) when every digit of $p$ belongs to $\{0, 1, 2, 5, 8\}$ and
all four seven-segment display symmetries yield primes: normal viewing, $180^\circ$ rotation
(reversing digit order), mirror reflection (reversing digit order while exchanging
$2 \leftrightarrow 5$), and upside-down mirror reflection (keeping digit order while exchanging
$2 \leftrightarrow 5$). Initial terms are $2, 5, 11, 101, 181, 1181, 1811, 18181, \dots$, and
$120121$ is the smallest term whose four orientations ($120121$, $121021$, $151051$, $150151$) are
pairwise distinct primes. Whether infinitely many decimal dihedral primes exist is open (and would
follow from infinitude of decimal repunit primes).

*References:*
- [Wikipedia: Dihedral prime](https://en.wikipedia.org/wiki/Dihedral_prime)
- [OEIS A134996](https://oeis.org/A134996)
- M. Keith, *Puzzle 39: The Mirrorable Numbers*,
  [Prime Puzzles](https://www.primepuzzles.net/puzzles/puzz_039.htm).
- C. K. Caldwell, *Dihedral prime*,
  [The Prime Glossary](https://t5k.org/glossary/page.php?sort=DihedralPrime).
-/

@[expose] public section

namespace DihedralPrime

/-- Checks whether a base-$10$ digit belongs to the seven-segment alphabet $\{0, 1, 2, 5, 8\}$. -/
def isDihedralDigit (d : ℕ) : Bool :=
  d == 0 || d == 1 || d == 2 || d == 5 || d == 8

/-- Seven-segment mirror involution exchanging $2 \leftrightarrow 5$ and fixing all other digits. -/
def swapTwoFive (d : ℕ) : ℕ :=
  if d = 2 then 5 else if d = 5 then 2 else d

/-- A natural number $p$ is a base-$10$ dihedral prime if $p$ is prime, all of its decimal digits
belong to $\{0, 1, 2, 5, 8\}$, and its upside-down, upside-down-mirrored, and mirrored digit
readings are all prime. -/
def IsDihedralPrime (p : ℕ) : Prop :=
  let ds := Nat.digits 10 p
  p.Prime ∧ (∀ d ∈ ds, isDihedralDigit d = true) ∧
    (Nat.ofDigits 10 ds.reverse).Prime ∧
    (Nat.ofDigits 10 (ds.map swapTwoFive)).Prime ∧
    (Nat.ofDigits 10 (ds.reverse.map swapTwoFive)).Prime

instance instDecidableIsDihedralPrime (p : ℕ) : Decidable (IsDihedralPrime p) := by
  unfold IsDihedralPrime
  infer_instance

/-- The digit-mirror map `swapTwoFive` is an involution. -/
@[category API, AMS 11]
theorem swapTwoFive_swapTwoFive (d : ℕ) : swapTwoFive (swapTwoFive d) = d := by
  unfold swapTwoFive
  split_ifs <;> omega

/-- $2$ satisfies `IsDihedralPrime`. -/
@[category test, AMS 11]
theorem isDihedralPrime_two : IsDihedralPrime 2 := by
  decide

/-- $5$ satisfies `IsDihedralPrime`. -/
@[category test, AMS 11]
theorem isDihedralPrime_five : IsDihedralPrime 5 := by
  decide

/-- $11$ satisfies `IsDihedralPrime`. -/
@[category test, AMS 11]
theorem isDihedralPrime_eleven : IsDihedralPrime 11 := by
  decide

/-- $101$ satisfies `IsDihedralPrime`. -/
@[category test, AMS 11]
theorem isDihedralPrime_101 : IsDihedralPrime 101 := by
  decide

/-- $1181$ satisfies `IsDihedralPrime`. -/
@[category test, AMS 11]
theorem isDihedralPrime_1181 : IsDihedralPrime 1181 := by
  have hd : Nat.digits 10 1181 = [1, 8, 1, 1] := by norm_num
  unfold IsDihedralPrime
  rw [hd]
  refine ⟨by norm_num, by decide, ?_, ?_, ?_⟩ <;> norm_num [Nat.ofDigits, swapTwoFive]

/-- $3$ fails `IsDihedralPrime` because its digit lies outside $\{0, 1, 2, 5, 8\}$. -/
@[category test, AMS 11]
theorem not_isDihedralPrime_three : ¬ IsDihedralPrime 3 := by
  decide

/-- $10$ fails `IsDihedralPrime` because it is composite. -/
@[category test, AMS 11]
theorem not_isDihedralPrime_ten : ¬ IsDihedralPrime 10 := by
  decide

/-- $151$ is a palindromic prime over $\{1, 5\}$ whose mirror image $121 = 11^2$ is composite. -/
@[category test, AMS 11]
theorem not_isDihedralPrime_151 : ¬ IsDihedralPrime 151 := by
  decide

/-- $120121$ satisfies `IsDihedralPrime`. -/
@[category test, AMS 11]
theorem isDihedralPrime_120121 : IsDihedralPrime 120121 := by
  have hd : Nat.digits 10 120121 = [1, 2, 1, 0, 2, 1] := by norm_num
  unfold IsDihedralPrime
  rw [hd]
  refine ⟨by norm_num, by decide, ?_, ?_, ?_⟩ <;> norm_num [Nat.ofDigits, swapTwoFive]

/-- Seven-segment display readings of $120121$ give the four distinct primes $120121$, $121021$,
$150151$, and $151051$. -/
@[category test, AMS 11]
theorem dihedral_readings_120121 :
    let ds := Nat.digits 10 120121
    [Nat.ofDigits 10 ds, Nat.ofDigits 10 ds.reverse,
      Nat.ofDigits 10 (ds.map swapTwoFive),
      Nat.ofDigits 10 (ds.reverse.map swapTwoFive)] =
      [120121, 121021, 150151, 151051] := by
  have hd : Nat.digits 10 120121 = [1, 2, 1, 0, 2, 1] := by norm_num
  rw [hd]
  decide

/--
Do infinitely many base-$10$ dihedral primes exist?
-/
@[category research open, question, AMS 11]
theorem dihedral_primes_infinite :
    {p : ℕ | IsDihedralPrime p}.Infinite := by
  sorry

end DihedralPrime
