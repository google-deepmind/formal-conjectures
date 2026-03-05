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
# Erdős Problem 1118

*Reference:* [erdosproblems.com/1118](https://www.erdosproblems.com/1118)

Let $f(z)$ be a non-constant entire function and let $E(c) = \{z : |f(z)| > c\}$. If $E(c)$ has
finite measure for some $c > 0$, what is the minimum growth rate of $f$? Moreover, must there
exist $c' < c$ such that $E(c')$ also has finite measure?

[Ca77] Camera, G., *A short proof of an extremal result of Hayman* (1977).

[Go79b] Gol'dberg, A. A., *The set of deficient values of meromorphic functions of finite order* (1979).
-/

open Complex Set MeasureTheory

namespace Erdos1118

/-- The maximum modulus of $f$ on the circle of radius $r$:
$M(r) = \sup\{\|f(z)\| : \|z\| = r\}$. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/-- The exceedance set $E(c) = \{z \in \mathbb{C} \mid \|f(z)\| > c\}$. -/
def exceedanceSet (f : ℂ → ℂ) (c : ℝ) : Set ℂ :=
  {z : ℂ | c < ‖f z‖}

/--
Erdős Problem 1118 — Hayman's conjecture, proved by Camera [Ca77]
and Gol'dberg [Go79b]:

Let $f(z)$ be a non-constant entire function such that for some $c > 0$, the set
$E(c) = \{z : |f(z)| > c\}$ has finite (Lebesgue) measure. Then
$$\int_0^\infty \frac{r}{\log \log M(r)} \, dr < \infty$$
where $M(r) = \max_{|z|=r} |f(z)|$. This growth condition is best possible.
-/
@[category research solved, AMS 28 30]
theorem erdos_1118 (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hnc : ∃ z : ℂ, f z ≠ f 0)
    (c : ℝ) (hc : 0 < c)
    (hfin : volume (exceedanceSet f c) < ⊤) :
    IntegrableOn (fun r => r / Real.log (Real.log (maxModulus f r)))
      (Ioi 0) volume := by
  sorry

/--
Erdős Problem 1118 — Negative answer to the second question, due to Gol'dberg [Go79b]:

There exists a non-constant entire function $f$ and $c > 0$ such that $E(c)$ has finite
measure, but $E(c')$ has infinite measure for all $0 < c' < c$.

Gol'dberg proved that $T = \{c > 0 : |E(c)| < \infty\}$ can equal $[m, \infty)$ or
$(m, \infty)$ for any $m > 0$.
-/
@[category research solved, AMS 28 30]
theorem erdos_1118.variants.negative_answer :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z : ℂ, f z ≠ f 0) ∧
      ∃ c : ℝ, 0 < c ∧
        volume (exceedanceSet f c) < ⊤ ∧
        ∀ c' : ℝ, 0 < c' → c' < c → volume (exceedanceSet f c') = ⊤ := by
  sorry

end Erdos1118
