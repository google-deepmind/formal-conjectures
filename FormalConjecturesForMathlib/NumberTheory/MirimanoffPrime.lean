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

public import FormalConjecturesForMathlib.NumberTheory.WieferichPrime

@[expose] public section

/-!
# Mirimanoff primes

A *Mirimanoff prime* is a prime $p$ with $3^{p-1} \equiv 1 \pmod{p^2}$, i.e. a Wieferich prime
to base $3$. The only known Mirimanoff primes are $11$ and $1006003$. The name comes from
Mirimanoff's 1910 result that a failure of the first case of Fermat's Last Theorem for the
exponent $p$ forces this congruence.

*References:*
- [OEIS A014127](https://oeis.org/A014127)
- D. Mirimanoff, *Sur le dernier théorème de Fermat*, C. R. Acad. Sci. Paris 150 (1910), 204–206.
-/

/--
**Mirimanoff prime**
A Mirimanoff prime is a prime $p$ with $3^{p-1} \equiv 1 \pmod{p^2}$, i.e. a Wieferich prime to
base $3$.
-/
abbrev IsMirimanoffPrime (p : ℕ) : Prop := IsWieferichPrimeBase 3 p
