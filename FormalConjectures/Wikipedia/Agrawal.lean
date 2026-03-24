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
# Agrawal's conjecture

Agrawal's conjecture is a stronger version of the theorem that forms the basis
of the AKS primality test. If true, it would significantly improve the
efficiency of primality testing.

The conjecture states that for coprime $n$ and $r$, if the polynomial congruence
$(X-1)^n \equiv X^n-1 \pmod{n, X^r-1}$ holds, then $n$ is either prime or $n^2 \equiv 1 \pmod{r}$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Agrawal%27s_conjecture)
- [AIM Math](https://aimath.org/WWN/primesinp/articles/html/50a/)
- [Paper](https://eprint.iacr.org/2009/008.pdf)
-/

open Polynomial

namespace AgrawalConjecture

/--
**Agrawal's Primality Conjecture.**

Does the congruence $(X-1)^n \equiv X^n - 1 \pmod{n, X^r-1}$ imply
$n$ is prime (with a specific exception for $n^2 \equiv 1 \pmod{r}$)?

While the "if" direction is a known theorem, the "only if" direction
remains a conjecture.
-/
@[category research open, AMS 11]
theorem agrawal_conjecture :
  answer(sorry) ↔
    ∀ (n r : ℕ), n > 1 → r > 0 → n.gcd r = 1 →
      let R := Polynomial (ZMod n)
      let X : R := Polynomial.X
      let I : Ideal R := Ideal.span ({X^r - 1} : Set R)
      Ideal.Quotient.mk I ((X - 1)^n) = Ideal.Quotient.mk I (X^n - 1) →
      (n.Prime ∨ (n^2 : ZMod r) = 1) := by
  sorry

/--
**Roman B. Popovych Conjecture.**
A stronger version of Agrawal's conjecture, which also considers the congruence
$(X+2)^n \equiv X^n + 2 \pmod{n, X^r-1}$.
If both congruences hold, then $n$ is either prime or $n^2 \equiv 1 \pmod{r}$.
This variant was proposed by Roman B. Popovych in 2018.
-/
@[category research open, AMS 11]
theorem agrawal_conjecture.variants.popovych :
  ∀ (n r : ℕ), n > 1 → r > 0 → n.gcd r = 1 →
    let R := Polynomial (ZMod n)
    let X : R := Polynomial.X
    let I : Ideal R := Ideal.span ({X^r - 1} : Set R)
    Ideal.Quotient.mk I ((X - 1)^n) = Ideal.Quotient.mk I (X^n - 1) →
    Ideal.Quotient.mk I ((X + 2)^n) = Ideal.Quotient.mk I (X^n + 2) →
    (n.Prime ∨ (n^2 : ZMod r) = 1) := by
  sorry

end AgrawalConjecture
