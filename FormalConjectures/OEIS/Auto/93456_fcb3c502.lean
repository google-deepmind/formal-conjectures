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

open Nat Finset

/--
A093456: Product of all composite numbers between $n(n-1)/2+1$ and $n(n+1)/2$ (including boundaries),
where $n(n-1)/2 = \binom{n}{2}$ and $n(n+1)/2 = \binom{n+1}{2}$.
-/
def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2

  -- A number k is composite if k > 1 and is not prime.
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime

  (Icc L R).filter is_composite |>.prod id


theorem a_one : a 1 = 1 := by sorry

theorem a_two : a 2 = 1 := by sorry

theorem a_three : a 3 = 24 := by sorry

theorem a_four : a 4 = 720 := by sorry

/--
Conjecture: There are finitely many numbers such that $a(n)$ is not $\equiv 0 \pmod{a(n-1)}$.
(Also mentioned in A093455.)
-/
theorem oeis_93456_conjecture_0 :
  Set.Finite {n : ℕ | n > 1 ∧ ¬ (a (n - 1) ∣ a n)} :=
by sorry
