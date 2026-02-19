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
# Conjectures associated with A56777

A56777 lists composite numbers $n$ satisfying both $\varphi(n+12) = \varphi(n) + 12$ and
$\sigma(n+12) = \sigma(n) + 12$.

The conjectures state identities connecting A56777 and prime quadruples (A7530), as
well as congruences satisfied by the members of A56777.

*References:* [A56777](https://oeis.org/A56777)
-/

open Nat
open scoped ArithmeticFunction.sigma

namespace OeisA56777

/-- A composite number $n$ is in the sequence A56777 if it satisfies both
$\varphi(n+12) = \varphi(n) + 12$ and $\sigma(n+12) = \sigma(n) + 12$. -/
def a (n : ℕ) : Prop :=
  ¬n.Prime ∧ 1 < n ∧ totient (n + 12) = totient n + 12 ∧ σ 1 (n + 12) = σ 1 n + 12

/-- A number $n$ comes from a prime quadruple $(p, p+2, p+6, p+8)$ if
$n = p(p+8)$ for some prime $p$ where $p$, $p+2$, $p+6$, $p+8$ are all prime. -/
def ComesFromPrimeQuadruple (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8)

/-- $65$ is in the sequence A56777. -/
@[category test, AMS 11]
theorem a_65 : a 65 := by
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · simp only [show (65 : ℕ) = 5 * 13 by norm_num]
    exact not_prime_mul (by norm_num) (by norm_num)
  · decide
  · decide

/-- $209$ is in the sequence A56777. -/
@[category test, AMS 11]
theorem a_209 : a 209 := by
  set_option maxRecDepth 1000 in
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · simp only [show (209 : ℕ) = 11 * 19 by norm_num]
    exact not_prime_mul (by norm_num) (by norm_num)
  · decide
  · decide

/-- Numbers coming from prime quadruples are in the sequence A56777. -/
@[category undergraduate, AMS 11]
theorem a_of_comesFromPrimeQuadruple {n : ℕ} (h : ComesFromPrimeQuadruple n) : a n := by
  sorry

/-- All members of the sequence A56777 come from prime quadruples. -/
@[category research open, AMS 11]
theorem comesFromPrimeQuadruple_of_a {n : ℕ} (h : a n) : ComesFromPrimeQuadruple n := by
  sorry

/-- Numbers coming from prime quadruples satisfy $n \equiv 65 \pmod{72}$. -/
@[category undergraduate, AMS 11]
theorem mod_72_of_comesFromPrimeQuadruple {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    n % 72 = 65 := by
  sorry

/-- Numbers coming from prime quadruples satisfy $n \equiv 9 \pmod{100}$. -/
@[category undergraduate, AMS 11]
theorem mod_100_of_comesFromPrimeQuadruple {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    n % 100 = 9 := by
  sorry

end OeisA56777
