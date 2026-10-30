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
# Erdős Problem 1195

*References:*
- [erdosproblems.com/1195](https://www.erdosproblems.com/1195)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115. [PDF](https://www.renyi.hu/~p_erdos/1980-03.pdf)
- [Ha70] Haight, J. A., *A linear set of infinite measure with no two points having integral
  ratio*. Mathematika (1970), 133--138.
- [HoGPT] Ho, Boon Suan and GPT-5.4 Pro, comments on Erdős Problem 1195. erdosproblems.com forum
  thread. [Forum](https://www.erdosproblems.com/forum/thread/1195)
- [Sc69] Schmidt, W. M., *Disproof of some conjectures on Diophantine approximations*. Studia Sci.
  Math. Hungar. (1969), 137-144.
- [Sz71] Szemerédi, E., *On a problem of W. Schmidt*. Studia Sci. Math. Hungar. (1971), 287--288.
-/

@[expose] public section

open Filter MeasureTheory

namespace Erdos1195

/-- The Lebesgue measure $\lvert S\cap (0,x)\rvert$ of $S\cap (0,x)$, as a real number. -/
noncomputable def countingFunction (S : Set ℝ) (x : ℝ) : ℝ :=
  (volume (S ∩ Set.Ioo 0 x)).toReal

/-- `IntegerRatioFree S` says that $x/y$ is not an integer for all distinct $x,y\in S$. Negative
integers are included. Since `x / 0 = 0` in Lean, a set with at least two points cannot contain
`0`; this does not affect measures. -/
def IntegerRatioFree (S : Set ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ∀ z : ℤ, x / y ≠ z

/-- `IsGrowthRate F` says that $F$ is nonnegative and non-decreasing on $[1,\infty)$ and tends to
infinity. We use $F:\mathbb{R}\to\mathbb{R}$; only its values on $[1,\infty)$ matter. -/
def IsGrowthRate (F : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Ici (1 : ℝ), 0 ≤ F x) ∧ MonotoneOn F (Set.Ici 1) ∧ Tendsto F atTop atTop

/-- `HasSet F` says that there is a measurable set $S$ of infinite measure such that $x/y$ is
never an integer for distinct $x,y\in S$, and $\lvert S\cap (0,x)\rvert\geq F(x)$ for all
sufficiently large $x$. -/
def HasSet (F : ℝ → ℝ) : Prop :=
  ∃ S : Set ℝ, MeasurableSet S ∧ volume S = ⊤ ∧ IntegerRatioFree S ∧
    ∀ᶠ x in atTop, F x ≤ countingFunction S x

/-- The answer: the growth rates $F$ with $\int_1^\infty F(x)/x^2\,dx<\infty$. For a non-negative
monotone $F$, `IntegrableOn` is equivalent to this integral being finite. -/
def erdos_1195.answer : Set (ℝ → ℝ) :=
  {F | IsGrowthRate F ∧ IntegrableOn (fun x ↦ F x / x ^ 2) (Set.Ici 1)}

set_option linter.style.formal_proof_palomar false in
/--
Let $S\subset \mathbb{R}$ be a set of infinite measure such that $x/y$ is never an integer for all
distinct $x,y\in S$.

How fast can $\lvert S\cap (0,x)\rvert$ tend to infinity?

A question of Erdős [Er80, p. 101]. Ho Boon Suan and GPT-5.4 Pro [HoGPT] settled this: if
$F:[1,\infty)\to [0,\infty)$ is a non-decreasing function tending to infinity, then there exists
such a set $S$ with
$\lvert S\cap (0,x)\rvert \geq F(x)$ if and only if
$$\int_1^\infty \frac{F(x)}{x^2}\mathrm{d}x < \infty.$$
Here $\lvert\cdot\rvert$ is Lebesgue measure, $S$ is measurable, and the inequality is required for
all sufficiently large $x$. The statement says that the set of such $F$ is exactly the answer.
-/
@[category research solved, question value, AMS 11 28, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1195.lean#L1933"]
theorem erdos_1195 :
    {F : ℝ → ℝ | IsGrowthRate F ∧ HasSet F} = erdos_1195.answer := by
  sorry

/--
Schmidt [Sc69] asked whether such a set exists. Haight [Ha70] constructed a measurable set
$E\subset(0,\infty)$ of infinite Lebesgue measure such that $x_1/x_2$ is never an integer for
distinct $x_1,x_2\in E$, and Szemerédi [Sz71] independently constructed such a set.
-/
@[category research solved, AMS 11 28]
theorem erdos_1195.variants.exists_set :
    ∃ S : Set ℝ, MeasurableSet S ∧ S ⊆ Set.Ioi 0 ∧ volume S = ⊤ ∧ IntegerRatioFree S := by
  sorry

end Erdos1195
