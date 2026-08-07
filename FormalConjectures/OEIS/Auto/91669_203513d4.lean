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

open Nat BigOperators

/--
A091669: $a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it as a function $\mathbb{N} \to \mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0 -- Sequence is defined for n >= 1.
  else
    let n_pred : ℕ := n.pred

    -- The numerator of the expression. Both factors are in ℕ.
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)

    -- The denominator is $n!$.
    let denominator : ℕ := n.factorial

    -- The division is exact, since the result is an integer sequence.
    numerator / denominator

-- We omit the proof placeholders for the example theorems
theorem a_one : a 1 = 1 := by sorry
theorem a_two : a 2 = 1 := by sorry
theorem a_three : a 3 = 2 := by sorry
theorem a_four : a 4 = 7 := by sorry


-- The formalization of the conjecture C A091669 from Jan 19 2020.
/--
Conjecture A091669: (for $n > 2$), if $n \mid a(n-1) + 2^{n-2}$, then $n$ is a prime
for which 2 is a primitive root modulo $n$ (A001122).
Note: We use `ZMod n` for the modulo ring and assume `totient` is available through `Mathlib`.
-/
theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) :=
by sorry
