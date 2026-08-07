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

public import Mathlib.Data.Nat.Factors

@[expose] public section

/-!
# Semiprimes

A semiprime is a natural number that is the product of exactly two prime factors (counting multiplicity).

*References:*
- [Wikipedia, Semiprime](https://en.wikipedia.org/wiki/Semiprime)
- [OEIS A001358](https://oeis.org/A001358)
-/

namespace Nat

/--
A natural number `n` is a *semiprime* if it has exactly two prime factors counting multiplicity,
that is, $\Omega(n) = 2$.
-/
def IsSemiprime (n : ℕ) : Prop :=
  n > 1 ∧ n.primeFactorsList.length = 2

instance (n : ℕ) : Decidable (n.IsSemiprime) := by
  unfold IsSemiprime
  infer_instance

/--
A natural number `n` is an *odd semiprime* if `n` is a semiprime and `n` is odd.
-/
def IsOddSemiprime (n : ℕ) : Prop :=
  n.IsSemiprime ∧ Odd n

instance (n : ℕ) : Decidable (n.IsOddSemiprime) := by
  unfold IsOddSemiprime
  infer_instance

end Nat
