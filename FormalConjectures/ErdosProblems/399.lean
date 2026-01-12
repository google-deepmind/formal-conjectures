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

/-!
# Erdős Problem 399

Is it true that there are no solutions to $n! = x^k \pm y^k$ with $x,y,n \in \mathbb{N}$,
with $xy > 1$ and $k > 2$?

*References:*
 - [erdosproblems.com/399](https://www.erdosproblems.com/399)
 - [Br32] R. Breusch, _Zur Verallgemeinerung des Bertrandschen Postulates_ (1932)
 - [ErOb37] P. Erdős and R. Obláth, _Über diophantische Gleichungen der Form $n!=x^p+y^p$ und
   $n!\pm m!=x^p$_ (1937)
 - [PoSh73] R. Pollack and H. Shapiro, _The next to last case of a factorial diophantine equation_
   (1973)
 - [Gu04] R. Guy, _Unsolved problems in number theory_ (2004)
-/

open Nat

namespace Erdos399

/-- The equation `n! = x^k + y^k`. -/
abbrev FactorialEqPowAdd (n x y k : ℕ) : Prop :=
  n ! = x ^ k + y ^ k

/-- The equation `n! = x^k - y^k`, encoded without subtraction as `n! + y^k = x^k`. -/
abbrev FactorialEqPowSub (n x y k : ℕ) : Prop :=
  n ! + y ^ k = x ^ k

/-- The disjunction `n! = x^k + y^k` or `n! = x^k - y^k`. -/
abbrev FactorialEqPowAddOrSub (n x y k : ℕ) : Prop :=
  FactorialEqPowAdd n x y k ∨ FactorialEqPowSub n x y k

/--
Is it true that there are no solutions to `n! = x^k ± y^k` with `x,y,n ∈ ℕ`, `x*y > 1`, and
`k > 2`?

The answer is no: Jonas Barfield found the counterexample `10! = 48^4 - 36^4` (equivalently,
`10! + 36^4 = 48^4`).
-/
@[category research solved, AMS 11]
theorem erdos_399 : answer(False) ↔
    ¬ ∃ (n x y k : ℕ), 1 < x * y ∧ 2 < k ∧ (n ! = x ^ k + y ^ k ∨ n ! + y ^ k = x ^ k) := by
  simp only [false_iff, Classical.not_not]
  exact ⟨10, 48, 36, 4, by decide⟩

/-- Erdős and Obláth proved there are no solutions when `x.Coprime y` and `k ≠ 4`. -/
@[category research solved, AMS 11]
theorem erdos_399.variants.erdos_oblath :
    ∀ {n x y k : ℕ}, x.Coprime y → 1 < x * y → 2 < k → k ≠ 4 →
      ¬ FactorialEqPowAddOrSub n x y k := by
  sorry

/-- Pollack and Shapiro proved there are no solutions to `n! = x^4 - 1`. -/
@[category research solved, AMS 11]
theorem erdos_399.variants.pollack_shapiro (n x : ℕ) : n ! + 1 ≠ x ^ 4 := by
  sorry

/--
Cambie observed that there are no solutions to `n! = x^4 + y^4` with `x.Coprime y` and `x*y > 1`.
-/
@[category research solved, AMS 11]
theorem erdos_399.variants.cambie {n x y : ℕ} :
    x.Coprime y → 1 < x * y → n ! ≠ x ^ 4 + y ^ 4 := by
  sorry

/--
The only solution to `n! = x^2 + y^2` with `x*y > 1` is `6! = 12^2 + 24^2` (up to swapping `x`
and `y`).
-/
@[category research solved, AMS 11]
theorem erdos_399.variants.sum_two_squares :
    ∀ {n x y : ℕ}, 1 < x * y → n ! = x ^ 2 + y ^ 2 →
      n = 6 ∧ (x = 12 ∧ y = 24 ∨ x = 24 ∧ y = 12) := by
  sorry

end Erdos399
