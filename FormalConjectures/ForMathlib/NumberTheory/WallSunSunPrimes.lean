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
**The Lucas numbers**
$L_0 = 2$, $L_1=1$, $L_{n+2} = L_{n+1}+L_n$
-/
def lucasNumber : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucasNumber (n + 1) + lucasNumber n

/--
**The Lucas sequence of the first kind**
$U_0(a,b) = 0$, $U_1(a,b)=1$, $U_{n+2}(a,b)=aU_{n+1}(a,b)-bU_n(a,b)$
-/
def lucasUNumberPQ (a b : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => a * lucasUNumberPQ a b (n + 1) - b * lucasUNumberPQ a b n

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
    lucasUNumberPQ a b index.toNat ≡ 0 [ZMOD (p^2)]
