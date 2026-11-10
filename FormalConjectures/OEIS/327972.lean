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
# Bitwise XOR of the Rule 30 and Rule 150 trajectories

The sequence $a(n)$ is the bitwise XOR of the complete rows at time $n$ of
Rules $30$ and $150$, both started from one black cell. Each row is encoded
as a binary integer with its leftmost cell as the most significant bit.
The sequence starts at $n=0$, with $a(0)=a(1)=0$.

*References:*
- [A327972](https://oeis.org/A327972)
- David L. Condrey, [Proof of the leading-bit formula](https://oeis.org/A327972/a327972.txt), 2026.
-/

@[expose] public section

namespace OeisA327972

/-- The complete row of Rule $30$ at time $n$, encoded as a binary integer. -/
def rule30Row : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    let r := rule30Row n
    Nat.xor r (Nat.lor (2 * r) (4 * r))

/-- The complete row of Rule $150$ at time $n$, encoded as a binary integer. -/
def rule150Row : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    let r := rule150Row n
    Nat.xor r (Nat.xor (2 * r) (4 * r))

/-- The bitwise XOR of the Rule $30$ and Rule $150$ rows at time $n$. -/
def a (n : ℕ) : ℕ := Nat.xor (rule30Row n) (rule150Row n)

@[category test, AMS 37 68]
theorem a_0 : a 0 = 0 := by decide

@[category test, AMS 37 68]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 37 68]
theorem a_2 : a 2 = 12 := by decide

@[category test, AMS 37 68]
theorem a_3 : a 3 = 4 := by decide

@[category test, AMS 37 68]
theorem a_4 : a 4 = 128 := by decide

@[category test, AMS 37 68]
theorem a_5 : a 5 = 384 := by decide

@[category test, AMS 37 68]
theorem a_6 : a 6 = 3404 := by decide

@[category test, AMS 37 68]
theorem a_7 : a 7 = 740 := by decide

@[category test, AMS 37 68]
theorem a_8 : a 8 = 37056 := by decide

@[category test, AMS 37 68]
theorem a_9 : a 9 = 127296 := by decide

/-- The periodic deficit $(1,2,1,4,1,2,1,5)$, indexed by $n \bmod 8$. -/
def leadingOffset (n : ℕ) : ℕ :=
  match n % 8 with
  | 1 | 5 => 2
  | 3 => 4
  | 7 => 5
  | _ => 1

/--
"For $n > 1$, $\lfloor\log_2(a(n))\rfloor = 2n - (1,2,1,4,1,2,1,5)$
according as $n \equiv 0,\ldots,7 \pmod 8$, respectively."

The formula was proposed by Alan Michael Gómez Calderón in 2023 and proved by
David L. Condrey in 2026 using the periodic evolution of the six cells nearest the left edge.
-/
@[category research solved, AMS 37 68]
theorem log2_eq (n : ℕ) (hn : 1 < n) : Nat.log2 (a n) = 2 * n - leadingOffset n := by
  sorry

end OeisA327972
