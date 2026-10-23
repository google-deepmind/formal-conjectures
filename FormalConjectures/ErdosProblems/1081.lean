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

public import FormalConjecturesUtil

/-!
# Erdős Problem 1081

*References:*
- [erdosproblems.com/1081](https://www.erdosproblems.com/1081)
- [Er76e] Erdős, P., *Problems and results on consecutive integers*.
  Publ. Math. Debrecen 23 (1976), 271-282.
- [Od81] Odoni, R. W. K., *A problem of Erdős on sums of two squarefull numbers*.
  Acta Arith. 39 (1981), 145-162.
- [BlGr06] Blomer, V. and Granville, A., *Estimates for representation numbers of quadratic
  forms*. Duke Math. J. 135 (2006), 261-302.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1081

/-- `IsSumOfTwoSquarefull n`: $n = a + b$ for squarefull numbers $a, b \geq 1$ (here $1$ is
squarefull). Allowing $a = 0$ or $b = 0$ would only add the $O(\sqrt{x})$ squarefull numbers up
to $x$, which does not affect the statements below. -/
def IsSumOfTwoSquarefull (n : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Powerful ∧ b.Powerful ∧ n = a + b

/-- $A(x)$: the number of integers $1 \leq n \leq x$ which are the sum of two squarefull
numbers. -/
noncomputable def A (x : ℝ) : ℕ :=
  {n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ IsSumOfTwoSquarefull n}.ncard

/-- $\alpha = 1 - 2^{-1/3} \approx 0.206299$, the exponent in the Blomer–Granville estimate. -/
noncomputable def alpha : ℝ := 1 - 2 ^ (-(1 : ℝ) / 3)

/-- $2 = 1 + 1$ is a sum of two squarefull numbers. -/
@[category test, AMS 11]
theorem isSumOfTwoSquarefull_two : IsSumOfTwoSquarefull 2 :=
  ⟨1, 1, one_pos, one_pos, Nat.Full.one_right 2, Nat.Full.one_right 2, rfl⟩

/--
Let $A(x)$ count the number of $n\leq x$ which are the sum of two squarefull numbers (a number
$m$ is squarefull if $p\mid m$ implies $p^2\mid m$). Is it true that
$$A(x) \sim c \frac{x}{\sqrt{\log x}}$$
for some $c>0$?

Odoni [Od81] proved this is false.
-/
@[category research solved, question, AMS 11]
theorem erdos_1081 :
    ¬ ∃ c > (0 : ℝ),
      (fun x : ℝ ↦ (A x : ℝ)) ~[atTop] fun x ↦ c * x / Real.sqrt (Real.log x) := by
  sorry

/--
Blomer and Granville [BlGr06] proved
$$A(x)= (\log\log x)^{O(1)}\frac{x}{(\log x)^{\alpha}}$$
where $\alpha=1-2^{-1/3}\approx 0.206299$: for some $C$ and all large $x$, $A(x)$ lies between
$(\log\log x)^{-C}$ and $(\log\log x)^{C}$ times $x/(\log x)^{\alpha}$.
-/
@[category research solved, AMS 11]
theorem erdos_1081.variants.blomer_granville :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      x / Real.log x ^ alpha / Real.log (Real.log x) ^ C ≤ A x ∧
        (A x : ℝ) ≤ x / Real.log x ^ alpha * Real.log (Real.log x) ^ C := by
  sorry

end Erdos1081
