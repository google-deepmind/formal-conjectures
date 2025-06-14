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

import Mathlib

/--
**The Lucas numbers**
$L_0 = 2$, $L_1=1$, $L_{n+2} = L_{n+1}+L_n$
-/
def lucasNumber : ℕ → ℕ
| 0 => 2
| 1 => 1
| (n+2) => lucasNumber (n+1) + lucasNumber n

/--
**The Lucas sequence of the first kind**
$U_0(a,b) = 0$, $U_1(a,b)=1$, $U_{n+2}(a,b)=aU_{n+1}(a,b)-bU_n(a,b)$
-/
def lucasUNumberPQ (a b : ℕ) : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n+2) => a * lucasNumber (n+1) - b * lucasNumber n

/--
**Wall–Sun–Sun prime**
A prime $p$ is a Wall–Sun–Sun prime if and only if $L_p \equiv 1 \pmod{p^2}$, where $L_p$ is Lucas numbers.
(One of the equivalent definitions)
-/
def IsWallSunSunPrime (p : ℕ) : Prop :=
  Prime p ∧ lucasNumber p ≡ 1 [MOD p^2]

/--
**Lucas–Wieferich prime**
A Lucas–Wieferich prime associated with $(a,b)$ is a prime $p$ such $U_{p-\varepsilon}(a,b) \equiv 0 \pmod{p^2}$
where $U(a,b)$ is the Lucas sequence of the first kind and $\varepsilon$ is the Legendre symbol.
-/
def IsLucasWieferichPrime (a b p : ℕ) : Prop :=
  p.Prime ∧ lucasUNumberPQ a b (p - legendreSym p (a ^ 2 - 4 * b)) ≡ 0 [MOD p^2]
