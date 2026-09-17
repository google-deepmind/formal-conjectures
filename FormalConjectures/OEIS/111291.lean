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
# Number of refactorable numbers (A033950) $\le 10^n$

A number $k$ is refactorable if its number of divisors, $\tau(k)$, divides $k$.

*References:*
- [A111291](https://oeis.org/A111291)
- [Co99] Colton, S., *Refactorable numbers - a machine invention*. J. Integer Seq. 2 (1999),
  Article 99.1.2.
- [Ze02] Zelinsky, J., *Tau numbers: a partial proof of a conjecture and other results*.
  J. Integer Seq. 5 (2002), Article 02.2.8.
- [Sp85] Spiro, C., *How often is the number of divisors of n a divisor of n?*
  J. Number Theory 21 (1985), 81--100.
-/

namespace OeisA111291

open Nat Finset Real

/-- Helper function: number of refactorable numbers $\le m$. -/
def countRefactorableNat (m : ℕ) : ℕ :=
  (Icc 1 m).filter (fun k => k.divisors.card ∣ k) |>.card

/--
`a n` is the number of refactorable numbers $\le 10^n$.
A number $k$ is refactorable if its number of divisors, $\tau(k)$, divides $k$.
-/
def a (n : ℕ) : ℕ :=
  countRefactorableNat (10 ^ n)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 16 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 92 := by native_decide

/--
`countRefactorable x` is the number of refactorable numbers $\le x$.
-/
noncomputable def countRefactorable (x : ℝ) : ℕ :=
  if _hx : x ≥ 1 then
    countRefactorableNat (Int.toNat (floor x))
  else
    0

/--
Simon Colton conjectures that the number of refactorable numbers less than $x$ is at least
$\frac{x}{2\log x}$. This is an asymptotic claim, so we state it for sufficiently large $x$.

In this form it is a theorem: Zelinsky [Ze02, Theorem 7] proved that for every $k$ the number of
refactorable numbers $\le n$ exceeds $k \pi(n)$ for all sufficiently large $n$, and
$\pi(n) \sim n / \log n$. It also follows from Spiro's asymptotic [Sp85], by which the count is
$\frac{x}{\sqrt{\log x}} (\log \log x)^{-1 + o(1)}$. See `colton_conjecture` for the
pointwise conjecture that remains open.
-/
@[category research solved, AMS 11]
theorem conjecture : ∀ᶠ x in Filter.atTop,
    (countRefactorable x : ℝ) ≥ x / (2 * Real.log x) := by
  sorry

/--
Colton's conjecture [Co99] as stated by Zelinsky [Ze02]: for every $n$, the number of
refactorable numbers $\le n$ is at least half the number of primes $\le n$, i.e.
$\pi(n) \le 2\,T(n)$.

Zelinsky [Ze02] proved this for all sufficiently large $n$ (see `conjecture`), with an explicit
bound of $7.42 \cdot 10^{13}$ beyond which it holds; the remaining range is open.
-/
@[category research open, AMS 11]
theorem colton_conjecture : ∀ n : ℕ, Nat.primeCounting n ≤ 2 * countRefactorableNat n := by
  sorry

/-- Colton's conjecture holds for $n \le 500$. -/
@[category test, AMS 11]
theorem colton_conjecture_le_500 : ∀ n ≤ 500, Nat.primeCounting n ≤ 2 * countRefactorableNat n := by
  native_decide

end OeisA111291
