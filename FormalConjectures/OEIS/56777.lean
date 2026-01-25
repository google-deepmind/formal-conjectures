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

open scoped ArithmeticFunction

/-!
# Conjectures associated with A056777

A056777 lists composite numbers $n$ satisfying both $\varphi(n+12) = \varphi(n) + 12$ and
$\sigma(n+12) = \sigma(n) + 12$.

The conjectures state identities connecting A056777 and prime quadruples (A007530), as
well as congruences satisfied by the members of A056777.

*References:* [oeis.org/A056777](https://oeis.org/A056777)
-/

namespace OeisA056777

/-- A composite number $n$ is in the sequence A056777 if it satisfies both
$\varphi(n+12) = \varphi(n) + 12$ and $\sigma(n+12) = \sigma(n) + 12$. -/
def a (n : ℕ) : Prop :=
  ¬n.Prime ∧ 1 < n ∧
  Nat.totient (n + 12) = Nat.totient n + 12 ∧
  σ 1 (n + 12) = σ 1 n + 12

/-- A number $n$ comes from a prime quadruple $(p, p+2, p+6, p+8)$ if
$n = p(p+8)$ for some prime $p$ where $p$, $p+2$, $p+6$, $p+8$ are all prime. -/
def comesFromPrimeQuadruple (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧
    n = p * (p + 8)

/-- $65$ is in the sequence A056777. -/
@[category test, AMS 11]
theorem a_65 : a 65 := by
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide

/-- $209$ is in the sequence A056777. -/
@[category test, AMS 11]
theorem a_209 : a 209 := by
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide

/-- Numbers coming from prime quadruples are in the sequence A056777. -/
@[category undergraduate, AMS 11]
theorem a_of_comesFromPrimeQuadruple (n : ℕ) (h : comesFromPrimeQuadruple n) : a n := by
  sorry

/-- All members of the sequence A056777 come from prime quadruples. -/
@[category research open, AMS 11]
theorem comesFromPrimeQuadruple_of_a (n : ℕ) (h : a n) : comesFromPrimeQuadruple n := by
  sorry

/-- Numbers coming from prime quadruples satisfy $n \equiv 65 \pmod{72}$. -/
@[category undergraduate, AMS 11]
theorem mod_72_of_comesFromPrimeQuadruple (n : ℕ) (h : comesFromPrimeQuadruple n) :
    n % 72 = 65 := by
  sorry

/-- Numbers coming from prime quadruples satisfy $n \equiv 9 \pmod{100}$. -/
@[category undergraduate, AMS 11]
theorem mod_100_of_comesFromPrimeQuadruple (n : ℕ) (h : comesFromPrimeQuadruple n) :
    n % 100 = 9 := by
  sorry

/-- All members of the sequence satisfy $n \equiv 65 \pmod{72}$. -/
@[category research open, AMS 11]
theorem mod_72_of_a (n : ℕ) (h : a n) : n % 72 = 65 := by
  sorry

end OeisA056777
