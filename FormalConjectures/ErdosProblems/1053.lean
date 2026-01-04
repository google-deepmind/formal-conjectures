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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1053

*Reference:* [erdosproblems.com/1053](https://www.erdosproblems.com/1053)

A question of Erdős, as reported in problem B2 of Guy's collection [Gu04].

[Gu04] Guy, Richard K., Unsolved problems in number theory. Third edition. Problem Books in
Mathematics. Springer-Verlag, New York, 2004.
-/

open Asymptotics Filter Real
open scoped ArithmeticFunction

namespace Erdos1053

/-- A natural number $n$ is $k$-perfect if $\sigma(n) = kn$, where $\sigma(n)$ is the sum of
divisors of $n$. These are also known as multiply perfect numbers. When $k = 2$, this is the
definition of a perfect number. -/
def IsMultiplyPerfect (k : ℕ) (n : ℕ) : Prop := σ 1 n = k * n

instance (k n : ℕ) : Decidable (IsMultiplyPerfect k n) :=
  inferInstanceAs (Decidable (σ 1 n = k * n))

/-- The perfectness level of a positive natural number $n$ is $\sigma(n) / n$.
For a $k$-perfect number, this equals $k$. -/
noncomputable def perfectnessLevel (n : ℕ) : ℕ := σ 1 n / n

/--
Call a number $k$-perfect if $\sigma(n) = kn$, where $\sigma(n)$ is the sum of the divisors of $n$.
Must $k = o(\log \log n)$?

That is, for any sequence of $k$-perfect numbers $n$ with $n \to \infty$, does the corresponding
sequence of $k$ values satisfy $k = o(\log \log n)$?

Guy further writes 'It has even been suggested that there may be only finitely many $k$-perfect
numbers with $k \geq 3$.' The largest $k$ for which a $k$-perfect number has been found is $k = 11$.
-/
@[category research open, AMS 11]
theorem erdos_1053 :
    (fun n ↦ (perfectnessLevel n : ℝ)) =o[atTop.comap (fun n ↦ n)]
      (fun n ↦ log (log n)) ↔ answer(sorry) := by
  sorry

/-- When $k = 2$, this is the definition of a perfect number for $n > 0$.
This follows from the fact that $\sigma(n) = \sum_{d \mid n} d$ includes $n$ itself,
so $\sigma(n) = 2n$ iff the sum of proper divisors equals $n$. -/
@[category API, AMS 11]
theorem isMultiplyPerfect_two_iff_perfect (n : ℕ) (hn : 0 < n) :
    IsMultiplyPerfect 2 n ↔ Nat.Perfect n := by
  sorry

/-- The number 6 is 2-perfect (a perfect number). -/
@[category test, AMS 11]
theorem isMultiplyPerfect_6 : IsMultiplyPerfect 2 6 := by
  native_decide

/-- The number 28 is 2-perfect (a perfect number). -/
@[category test, AMS 11]
theorem isMultiplyPerfect_28 : IsMultiplyPerfect 2 28 := by
  native_decide

/-- The number 120 is 3-perfect (a triperfect number). -/
@[category test, AMS 11]
theorem isMultiplyPerfect_120 : IsMultiplyPerfect 3 120 := by
  native_decide

/-- The number 672 is 3-perfect (a triperfect number). -/
@[category test, AMS 11]
theorem isMultiplyPerfect_672 : IsMultiplyPerfect 3 672 := by
  native_decide

/-- The number 30240 is 4-perfect (a quadruperfect number). -/
@[category test, AMS 11]
theorem isMultiplyPerfect_30240 : IsMultiplyPerfect 4 30240 := by
  native_decide

/--
It has been suggested that there may be only finitely many $k$-perfect numbers with $k \geq 3$.
-/
@[category research open, AMS 11]
theorem erdos_1053.variants.finitely_many_k_ge_3 :
    Set.Finite {n : ℕ | ∃ k ≥ 3, IsMultiplyPerfect k n} ↔ answer(sorry) := by
  sorry

end Erdos1053
