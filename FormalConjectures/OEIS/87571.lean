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
# Smallest prime formed by concatenation $n, n-1, \dots, n-k$

$a(n)$ is the smallest prime which has the form of the concatenation
$n, n-1, n-2, \dots, n-k$ for some $k < n$, or $0$ if no such prime exists.

*References:*
- [A087571](https://oeis.org/A087571)-/

namespace OeisA87571

/-- Concatenate a list of numbers into a list of decimal digits in most-significant-first order. -/
def getAllDigitsMsf (L : List ℕ) : List ℕ :=
  List.flatten (L.map fun k => (Nat.digits 10 k).reverse)

/-- Convert a list of decimal digits (most significant first) to a natural number. -/
def ofDigitsMsf (D : List ℕ) : ℕ :=
  D.foldl (fun acc d => acc * 10 + d) 0

/-- Concatenation of numbers $n, n-1, \dots, n-k$. -/
def concatNum (n : ℕ) (k : ℕ) : ℕ :=
  ofDigitsMsf (getAllDigitsMsf ((List.range (k + 1)).map fun i => n - i))

/-- Smallest prime of the form $n, n-1, \dots, n-k$ for $k < n$, or $0$ if none exists. -/
def a (n : ℕ) : ℕ :=
  match ((List.range n).map (concatNum n)).find? Nat.Prime with
  | some p => p
  | none => 0

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide +native

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 43 := by decide +native

/--
Conjecture: There are infinitely many composite numbers $n$ such that $a(n)$ is nonzero.-/
@[category research open, AMS 11]
theorem conjecture (M : ℕ) : ∃ n > M, 1 < n ∧ ¬ n.Prime ∧ a n ≠ 0 := by
  sorry

end OeisA87571
