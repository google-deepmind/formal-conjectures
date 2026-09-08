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
# Recurrence $a(n+2) = |a(n+1)a(n) - a(n)a(n+1)|$ via concatenation

The sequence starts with $a(1) = 0, a(2) = 1$. For $n \ge 1$,
$$a(n+2) = |\text{concat}(a(n+1), a(n)) - \text{concat}(a(n), a(n+1))|$$
where concatenation is in decimal representation.

*References:*
- [A070823](https://oeis.org/A070823)
-/

namespace OeisA70823

/-- Number of digits of a natural number $n$ in base 10 (with 1 digit for 0). -/
def numDigitsBase10 (n : ℕ) : ℕ :=
  if n = 0 then 1 else Nat.log 10 n + 1

/-- Concatenate $x$ followed by $y$ in base 10. -/
def concatenate (x y : ℕ) : ℕ :=
  x * 10 ^ (numDigitsBase10 y) + y

/-- The sequence $a(1)=0, a(2)=1, a(n+2)=|\text{concat}(a(n+1),a(n))-\text{concat}(a(n),a(n+1))|$. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 =>
    let cat1 := concatenate (a (n + 2)) (a (n + 1))
    let cat2 := concatenate (a (n + 1)) (a (n + 2))
    ((cat1 : ℤ) - (cat2 : ℤ)).natAbs

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 9 := by
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 72 := by
  decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 243 := by
  decide

/--
$a(n) \equiv 0 \pmod 3$ if $n > 2$. Is $a(n)$ always of the form $2^j \cdot 3^k \cdot s$
where $s$ is a squarefree number?

Answer: False, $a(20)$ is divisible by $13^2$ but not by $13^3$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a070823-counterexample/blob/51399770e734616c6463be034e41f7469991d752/lean/OeisA70823CounterexampleFC.lean#L72-L81"]
theorem conjecture :
    answer(False) ↔ ∀ n : ℕ, 2 < n →
      a n ≡ 0 [MOD 3] ∧
        ∃ j k s : ℕ, a n = 2 ^ j * 3 ^ k * s ∧ Squarefree s := by
  sorry

end OeisA70823
