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
# Primes of the form 2^n + 2^i + 1

There are infinite primes of the form $2^n + 2^i + 1$, with $0 < i < n$.
See Wagstaff (2001) where this conjecture is posed.

*References:*
- [A81091](https://oeis.org/A81091)
- Samuel S. Wagstaff, Jr., [Prime Numbers with a fixed number of one bits or zero bits in their binary representation](http://projecteuclid.org/euclid.em/999188636), Exp. Math. vol. 10, issue 2 (2001) 267.
-/

namespace OeisA81091

/-- Primes with $m$ one bits in their binary representation. -/
def isPrimeBitsSet (m p : ℕ) : Prop :=
  p.Prime ∧ p.bits.count true = m

/-- Primes in A81091 have exactly $3$ set bits in binary representation ($2^n + 2^i + 1$). -/
def A (p : ℕ) : Prop :=
  isPrimeBitsSet 3 p

@[category test, AMS 11]
theorem a_7 : A 7 := by unfold A isPrimeBitsSet; decide +native

@[category test, AMS 11]
theorem a_11 : A 11 := by unfold A isPrimeBitsSet; decide +native

@[category test, AMS 11]
theorem a_13 : A 13 := by unfold A isPrimeBitsSet; decide +native

@[category test, AMS 11]
theorem a_19 : A 19 := by unfold A isPrimeBitsSet; decide +native

@[category test, AMS 11]
theorem a_37 : A 37 := by unfold A isPrimeBitsSet; decide +native

/--
**Conjecture (A81091)**: There are infinite primes of the form $2^n + 2^i + 1$,
with $0 < i < n$.
-/
@[category research open, AMS 11]
theorem conjectureA81091 :
    answer(sorry) ↔ Set.Infinite {p : ℕ | A p} := by
  sorry

-- TODO(Paul-Lez): add result that for m ≥ 3, there is no prime number with precisely 2m bits, exactly two of which are zero bits.

end OeisA81091
