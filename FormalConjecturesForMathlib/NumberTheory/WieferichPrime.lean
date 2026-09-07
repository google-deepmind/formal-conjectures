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

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

/-!
# Wieferich primes

A prime $p$ is a *Wieferich prime to base $a$* if $a^{p-1} \equiv 1 \pmod{p^2}$, i.e. if the
congruence of Fermat's little theorem holds modulo $p^2$ rather than just modulo $p$.
A *Wieferich prime* is a Wieferich prime to base $2$. The only known Wieferich primes are $1093$
and $3511$.

*References:*
- [Wikipedia, Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime)
- [OEIS A001220](https://oeis.org/A001220)
-/

/--
**Wieferich prime to base `a`**
A prime $p$ is a Wieferich prime to base $a$ if $a^{p-1} \equiv 1 \pmod{p^2}$.
-/
@[mk_iff]
structure IsWieferichPrimeBase (a p : ℕ) : Prop where
  prime : p.Prime
  pow_modEq : a ^ (p - 1) ≡ 1 [MOD p ^ 2]

instance (a p : ℕ) : Decidable (IsWieferichPrimeBase a p) :=
  decidable_of_iff _ (isWieferichPrimeBase_iff a p).symm

/--
**Wieferich prime**
A Wieferich prime is a prime $p$ with $2^{p-1} \equiv 1 \pmod{p^2}$, i.e. a Wieferich prime to
base $2$.
-/
abbrev IsWieferichPrime (p : ℕ) : Prop := IsWieferichPrimeBase 2 p
