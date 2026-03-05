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
# Erdős Problem 1081

*Reference:* [erdosproblems.com/1081](https://www.erdosproblems.com/1081)

Let $A(x)$ count the number of $n \leq x$ which are the sum of two squarefull numbers
(a number $m$ is squarefull if $p \mid m$ implies $p^2 \mid m$). Is it true that
$A(x) \sim c \cdot x / \sqrt{\log x}$ for some $c > 0$?

This was disproved by Odoni [Od81].

[Er76e] Erdős, P.

[Od81] Odoni, R. W. K.
-/

open Filter Classical

namespace Erdos1081

/-- A natural number is squarefull (powerful) if it is positive and for every
prime $p$ dividing it, $p^2$ also divides it. -/
def IsSquarefull (m : ℕ) : Prop :=
  0 < m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

/-- A natural number is expressible as the sum of two squarefull numbers. -/
def IsSumOfTwoSquarefull (n : ℕ) : Prop :=
  ∃ a b : ℕ, IsSquarefull a ∧ IsSquarefull b ∧ n = a + b

/-- $A(x)$: the count of natural numbers $n$ in $[1, x]$ that are sums of two
squarefull numbers. -/
noncomputable def countA (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => IsSumOfTwoSquarefull n)).card

/--
Erdős Problem 1081 [Er76e] (DISPROVED):

Is it true that there exists $c > 0$ such that $A(x) \sim c \cdot x / \sqrt{\log x}$, i.e.,
$$A(x) \cdot \sqrt{\log x} / x \to c \text{ as } x \to \infty?$$

This was disproved by Odoni [Od81].
-/
@[category research solved, AMS 11]
theorem erdos_1081 : answer(False) ↔
    ∃ c : ℝ, c > 0 ∧
    Tendsto (fun x : ℕ =>
      (countA x : ℝ) * Real.sqrt (Real.log (x : ℝ)) / (x : ℝ))
      atTop (nhds c) := by
  sorry

end Erdos1081
