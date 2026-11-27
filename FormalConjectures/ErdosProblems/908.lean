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
# Erdős Problem 908

*References:*
- [erdosproblems.com/908](https://www.erdosproblems.com/908)
- [Er81b] Erdős, P., *My Scottish Book 'Problems'*. The Scottish Book (1981), 27-35.
- [Er82e] Erdős, P., *Some of my favourite problems which recently have been solved*. (1982),
  59-79.
- [La80] Laczkovich, M., *Functions with measurable differences*. Acta Math. Acad. Sci. Hungar.
  (1980), 217-235.
-/

@[expose] public section

open MeasureTheory

namespace Erdos908

/--
Let $f:\mathbb{R}\to \mathbb{R}$ be such that $f(x+h)-f(x)$ is measurable for every $h>0$. Is it
true that
$$f=g+h+r$$
where $g$ is measurable, $h$ is additive (so $h(x+y)=h(x)+h(y)$), and $r(x+h)-r(x)=0$ for every
$h$ and almost all (depending on $h$) $x$?

A conjecture of de Bruijn and Erdős. Answered in the affirmative by Laczkovich [La80].

Measurable means Lebesgue measurable, which is formalised as `AEMeasurable` with respect to the
Lebesgue measure. The problem page asks for $g$ continuous; that version is false, see
`erdos_908.variants.continuous`.
-/
@[category research solved, question, AMS 26 28 39]
theorem erdos_908 :
    ∀ f : ℝ → ℝ, (∀ h : ℝ, 0 < h → AEMeasurable fun x ↦ f (x + h) - f x) →
      ∃ g a r : ℝ → ℝ, AEMeasurable g ∧ (∀ x y, a (x + y) = a x + a y) ∧
        (∀ h : ℝ, ∀ᵐ x, r (x + h) - r x = 0) ∧ f = g + a + r := by
  sorry

/--
The decomposition $f=g+h+r$ of `erdos_908` does not always exist with $g$ continuous.

For example, let $f$ be the indicator function of $[0,1]$ and suppose $f=g+h+r$. For every $t$,
the function $x\mapsto f(x+t)-f(x)-h(t)$ agrees almost everywhere with the continuous function
$x\mapsto g(x+t)-g(x)$. This is impossible for $t=1/2$, since $f(x+1/2)-f(x)$ equals $1$ on
$(-1/2,0)$ and $0$ on $(0,1/2)$.
-/
@[category research solved, AMS 26 28 39]
theorem erdos_908.variants.continuous :
    ¬ ∀ f : ℝ → ℝ, (∀ h : ℝ, 0 < h → AEMeasurable fun x ↦ f (x + h) - f x) →
      ∃ g a r : ℝ → ℝ, Continuous g ∧ (∀ x y, a (x + y) = a x + a y) ∧
        (∀ h : ℝ, ∀ᵐ x, r (x + h) - r x = 0) ∧ f = g + a + r := by
  sorry

end Erdos908
