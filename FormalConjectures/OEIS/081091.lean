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
  * Samuel S. Wagstaff, Jr., [Prime Numbers with a fixed number of one bits or zero bits in their binary 
     representation](http://projecteuclid.org/euclid.em/999188636), Exp. Math. vol. 10, issue 2 (2001) 267.
  * [A081091](https://oeis.org/A081091)
  -/

  namespace OeisA081091

  /-- Primes with $m$ one bits in their binary representation. -/
  def isPrimeBitsSet (m p : ℕ) : Prop :=
    p.Prime ∧ p.bits.count true = m

  /--
  **Conjecture (A081091)**: There are infinite primes of the form $2^n + 2^i + 1$,
  with $0 < i < n$.
  -/
  @[category research open, AMS 11]
  theorem conjectureA081091 :
      answer(sorry) ↔ Set.Infinite {p : ℕ | isPrimeBitsSet 3 p} := by
    sorry

  end OeisA081091
