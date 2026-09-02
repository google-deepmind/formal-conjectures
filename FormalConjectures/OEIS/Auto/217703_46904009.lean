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

open Int
open Polynomial

/--
A217703: $a(0)=1$, $a(1)=0$, and $a(n+1) = 2n(n+1)a(n)-n^4 a(n-1)$ for $n>0$.
-/
def A217703 (n : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | 1 => 0
  | k + 2 =>
    -- The index being computed is $k+2$. The OEIS coefficient index is $n = k+1$.
    -- Recurrence: A(k+2) = 2(k+1)(k+2) A(k+1) - (k+1)^4 A(k)
    let m : ℤ := (k + 1 : ℕ)
    let a_k_plus_1 : ℤ := A217703 (k + 1)
    let a_k : ℤ := A217703 k
    (2 * m * (m + 1)) * a_k_plus_1 - (m ^ 4) * a_k

theorem a_zero : A217703 0 = 1 := by
  rfl

theorem a_one : A217703 1 = 0 := by
  rfl

/--
A217703 related polynomials: $S_0(x)=1$, $S_1(x)=x$, and $S_{n+1}(x)=(x+2n(n+1))S_n(x)-n^4 S_{n-1}(x)$ for $n>0$.
$S_n(x)$ is a polynomial with integer coefficients.
-/
noncomputable def Sn (n : ℕ) : Polynomial ℤ :=
  match n with
  | 0 => 1
  | 1 => X
  | k + 2 =>
    -- $n = k+1$ in the OEIS recurrence $S_{n+1}$
    let m : ℕ := k + 1
    let Sm : Polynomial ℤ := Sn m
    let S_m_minus_1 : Polynomial ℤ := Sn k

    let m_int : ℤ := m
    let coeff_int : ℤ := 2 * m_int * (m_int + 1)
    let coeff_poly : Polynomial ℤ := Polynomial.X + Polynomial.C coeff_int
    coeff_poly * Sm - Polynomial.C (m_int ^ 4) * S_m_minus_1

/--
Conjectures from OEIS A217703:
(i) $S_n(x)$ is irreducible over the field of rational numbers for every $n=1,2,3,...$
-/
theorem oeis_217703_conjecture_i :
  ∀ (n : ℕ), 1 ≤ n → Irreducible (Polynomial.map (Int.castRingHom ℚ) (Sn n)) := by
  sorry
