/-
Copyright 2025 The Formal Conjectures Authors.

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

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! #

*References:*
- [Wikipedia, Lucas_sequence](https://en.wikipedia.org/wiki/Lucas_sequence)
- [Wikipedia, Wall–Sun–Sun prime](https://en.wikipedia.org/wiki/Wall%E2%80%93Sun%E2%80%93Sun_prime)
- [Wikipedia, Wieferich prime](https://en.wikipedia.org/wiki/Lucas%E2%80%93Wieferich_prime)
-/

/--
**The Lucas sequence of the first kind**
$U_0(P, Q) = 0$, $U_1(P, Q)=1$, $U_{n+2}(P, Q)=PU_{n+1}(P, Q)-QU_n(P, Q)$
-/
def LucasSequence.U (P Q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => P * LucasSequence.U P Q (n + 1) - Q * LucasSequence.U P Q n

/--
**The Lucas sequence of the second kind**
$V_0(P, Q) = 0$, $V_1(P, Q)=P$, $V_{n+2}(P, Q)=PV_{n+1}(P, Q)-QV_n(P, Q)$
-/
def LucasSequence.V (P Q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => P
  | n + 2 => P * LucasSequence.V P Q (n + 1) - Q * LucasSequence.V P Q n

/--
**The Lucas numbers**
$L_0 = 2$, $L_1=1$, $L_{n+2} = L_{n+1}+L_n$
-/
def lucasNumber : ℕ → ℤ := LucasSequence.V 1 (-1)

/--
**Wall–Sun–Sun prime**
A prime $p$ is a Wall–Sun–Sun prime if and only if $L_p \equiv 1 \pmod{p^2}$, where $L_p$ is
the $p$-th Lucas number.
-/
structure IsWallSunSunPrime (p : ℕ) : Prop where
  prime : p.Prime
  lucasNumber_modeq : lucasNumber p ≡ 1 [ZMOD (p ^ 2)]

/--
**Lucas–Wieferich prime**
A Lucas–Wieferich prime associated with $(a,b)$ is a prime $p$ such $U_{p-\varepsilon}(a,b) \equiv 0 \pmod{p^2}$
where $U(a,b)$ is the Lucas sequence of the first kind and $\varepsilon$ is the Legendre symbol
$\left({\tfrac {a^{2}-4b}{p}}\right)$
-/
structure IsLucasWieferichPrime (a b p : ℕ) : Prop where
  prime : p.Prime
  modeq :
    letI index := p - jacobiSym p (a^2 - 4*b)
    LucasSequence.U a b index.toNat ≡ 0 [ZMOD (p^2)]
