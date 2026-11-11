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
# Odd composite numbers not of the form prime $+ 2 \times \text{square}$

Christian Goldbach conjectured in a 1752 letter to Leonhard Euler that every odd integer $n > 1$
can be written in the form $p + 2a^2$ for some prime $p$ and integer $a \ge 0$ (allowing $a = 0$
when $n$ itself is prime). Moritz Abraham Stern (1854) found that the odd composite numbers
$5777 = 53 \times 109$ and $5993 = 13 \times 461$ cannot be written in this form.

Laurent Hodges (1993) and Richard K. Guy (*Unsolved Problems in Number Theory*, Problem A19) asked
whether $5777$ and $5993$ are the only odd composite numbers not of the form $p + 2a^2$.

*References:*
- [A060003](https://oeis.org/A060003)
- [A058320](https://oeis.org/A058320)
- Richard K. Guy, *Unsolved Problems in Number Theory* (3rd ed.), Problem A19.
- Laurent Hodges, "A lesser-known Goldbach conjecture", *Mathematics Magazine* 66 (1993), 45–47.
-/

@[expose] public section

namespace OeisA60003

/-- A natural number `n` is representable as a prime plus twice a square ($n = p + 2a^2$ with
$p$ prime and $a \ge 0$). -/
def IsPrimePlusTwiceSquare (n : ℕ) : Prop :=
  ∃ a ≤ n, 2 * a ^ 2 ≤ n ∧ Nat.Prime (n - 2 * a ^ 2)

instance (n : ℕ) : Decidable (IsPrimePlusTwiceSquare n) :=
  inferInstanceAs (Decidable (∃ a ≤ n, 2 * a ^ 2 ≤ n ∧ Nat.Prime (n - 2 * a ^ 2)))

/-- `5777 = 53 * 109` is the first odd composite number not of the form $p + 2a^2$. -/
@[category test, AMS 11]
theorem stern_5777 : Odd 5777 ∧ ¬ Nat.Prime 5777 ∧ ¬ IsPrimePlusTwiceSquare 5777 := by
  decide +kernel

/-- `5993 = 13 * 461` is the second odd composite number not of the form $p + 2a^2$. -/
@[category test, AMS 11]
theorem stern_5993 : Odd 5993 ∧ ¬ Nat.Prime 5993 ∧ ¬ IsPrimePlusTwiceSquare 5993 := by
  decide +kernel

/-- Goldbach's 1752 conjecture that every odd composite number is of the form $p + 2a^2$ is false. -/
@[category research solved, AMS 11]
theorem not_forall_odd_composite_isPrimePlusTwiceSquare :
    ¬ ∀ n : ℕ, Odd n → 1 < n → ¬ Nat.Prime n → IsPrimePlusTwiceSquare n := by
  intro h
  exact stern_5777.2.2 (h 5777 stern_5777.1 (by decide) stern_5777.2.1)

/--
"Are there any other odd composite numbers beside 5777 and 5993 that cannot be written as
$p + 2a^2$?" — Richard K. Guy, *Unsolved Problems in Number Theory*, Problem A19;
see also [A060003](https://oeis.org/A060003).
-/
@[category research open, question, AMS 11]
theorem no_other_odd_composite_stern_number :
    ∀ n > 5993, Odd n → ¬ Nat.Prime n → IsPrimePlusTwiceSquare n := by
  sorry

end OeisA60003
