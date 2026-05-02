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
# Normality of mathematical constants

A real number $x$ is **normal in base $b$** if every digit $d \in \{0, 1, \ldots, b-1\}$
appears with asymptotic frequency $1/b$ in the base-$b$ expansion of $x$: formally,
$$\lim_{n \to \infty} \frac{N_d(n)}{n} = \frac{1}{b}$$
where $N_d(n)$ counts occurrences of digit $d$ among the first $n$ digits.
A number that is normal in every integer base $b \ge 2$ is called **absolutely normal**.

Despite extensive empirical evidence—billions of digits have been computed for $\pi$,
$e$, and $\sqrt{2}$, all showing near-uniform digit distribution—it is an open problem
whether any of the classical constants $\pi$, $e$, $\sqrt{2}$, $\ln 2$, or $\varphi$ is
normal in any base.

*References:*
* [Wikipedia (Normal number)](https://en.wikipedia.org/wiki/Normal_number)
* [Wikipedia (Pi)](https://en.wikipedia.org/wiki/Pi)
-/

open Real Filter

open scoped goldenRatio

namespace NormalNumber

/-- The `n`-th digit (0-indexed) after the radix point in the base-`b` expansion of `x`.
Concretely, `digitSeq b x n = ⌊b^(n+1) · {x}⌋ mod b` where `{x}` is the fractional part. -/
noncomputable def digitSeq (b : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ % b

/-- `x` is **normal in base `b`** if every digit `d < b` appears with asymptotic
frequency `1/b` in the base-`b` fractional expansion of `x`. -/
noncomputable def IsNormalInBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ d : ℕ, d < b → Tendsto (fun n : ℕ => (((Finset.range n).filter (fun k => digitSeq b x k = d)).card : ℝ) / (n : ℝ))
      atTop (nhds (1 / (b : ℝ)))

/-- `x` is **absolutely normal** if it is normal in every integer base `b ≥ 2`. -/
noncomputable def IsAbsolutelyNormal (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → IsNormalInBase b x

/--
$\pi$ is normal in base 10.
-/
@[category research open, AMS 11]
theorem pi_normal_base_ten : IsNormalInBase 10 π := by
  sorry

end NormalNumber
