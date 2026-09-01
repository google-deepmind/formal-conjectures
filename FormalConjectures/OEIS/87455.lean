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
# Expansion of $(1 - x)/(1 - 2 x + 3 x^2)$

This sequence is the expansion of $(1 - x)/(1 - 2 x + 3 x^2)$ in powers of $x$.
It satisfies the linear recurrence relation $a(n) = 2 a(n-1) - 3 a(n-2)$ for $n \ge 2$,
with initial values $a(0)=1$ and $a(1)=1$.

*References:*
- [A087455](https://oeis.org/A087455)-/

namespace OeisA87455

/-- The primary defining sequence `a`, satisfying $a(n) = 2 a(n-1) - 3 a(n-2)$ for $n \ge 2$,
with initial values $a(0)=1$ and $a(1)=1$. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * a (n + 1) - 3 * a n

/-- The leading decimal digit of a natural number. -/
def leadingDigit (n : ℕ) : ℕ :=
  n / 10 ^ ((Nat.digits 10 n).length - 1)

/-- A sequence of integers satisfies Benford's law if for each digit $d \in \{1, \dots, 9\}$,
the asymptotic relative frequency of terms with leading decimal digit $d$ is $\log_{10}(1 + 
    1/d)$. -/
def SatisfiesBenford (s : ℕ → ℤ) : Prop :=
  ∀ d ∈ Finset.Icc 1 9,
    Filter.Tendsto
      (fun N : ℕ =>
        ((Finset.range N).filter (fun n => leadingDigit (s n).natAbs = d)).card / (N : ℝ))
      Filter.atTop
      (nhds (Real.log (1 + 1 / (d : ℝ)) / Real.log 10))

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = -1 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = -5 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = -7 := by rfl

/--
It is an open question whether or not this sequence satisfies Benford's law
[Berger-Hill, 2017; Arno Berger, email, Jan 06 2017]. - N. J. A. Sloane, Feb 08 2017-/
@[category research open, AMS 11 60]
theorem conjecture : answer(sorry) ↔ SatisfiesBenford a := by
  sorry

end OeisA87455
