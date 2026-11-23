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
public import FormalConjectures.Wikipedia.HardyLittlewood

/-!
# Erdős Problem 855

*References:*
- [erdosproblems.com/855](https://www.erdosproblems.com/855)
- [CEFVV25] Chahal, B., Elma, E., Fellini, N., Vatwani, A. and Vo, D. N. T., *On the second
  Hardy–Littlewood conjecture*. [arXiv:2503.02766](https://arxiv.org/abs/2503.02766) (2025).
  Published in Acta Arith. (2026), doi:10.4064/aa250808-4-11. Statement numbers below refer to
  the arXiv version.

This is an "eventually" formulation of the Second Hardy–Littlewood conjecture.
-/

@[expose] public section

open Asymptotics Filter
open scoped Nat.Prime

namespace Erdos855

/--
Erdős Problem 855 (Segal's conjecture): $\pi(x + y) \le \pi(x) + \pi(y)$
for all sufficiently large $x, y$, i.e. for all $x, y \ge N$ for some $N$.
-/
@[category research open, question, AMS 11]
theorem erdos_855 :
    ∀ᶠ (xy : ℕ × ℕ) in atTop ×ˢ atTop, π (xy.1 + xy.2) ≤ π xy.1 + π xy.2 := by
  sorry

/--
Assuming the Riemann Hypothesis, Chahal, Elma, Fellini, Vatwani and Vo [CEFVV25, Corollary 1.2]
showed that for every $\varepsilon > 0$ there is $x_\varepsilon$ such that
$\pi(x + y) \le \pi(x) + \pi(y)$ for all integers $x \ge x_\varepsilon$ and
$$
  \frac{(2 + \varepsilon) x^{1/2} \log^2 x}{8\pi} \le y \le x.
$$
The restriction $y \le x$ loses nothing since the inequality is symmetric in $x$ and $y$. This
does not settle `erdos_855`, which also asks about $y$ below $x^{1/2} \log^2 x$.
-/
@[category research solved, AMS 11]
theorem erdos_855.variants.riemann_hypothesis (hRH : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ y : ℕ,
      (2 + ε) * Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) ≤ y → y ≤ x →
        π (x + y) ≤ π x + π y := by
  sorry

/--
Assuming the Riemann Hypothesis, Chahal, Elma, Fellini, Vatwani and Vo [CEFVV25, Corollary 1.5]
showed that the number of exceptions is small:
$$
  \#\{2 \le y \le x \le X : \pi(x + y) > \pi(x) + \pi(y)\} \ll X^{3/2} \log^2 X.
$$
-/
@[category research solved, AMS 11]
theorem erdos_855.variants.riemann_hypothesis_exceptions (hRH : RiemannHypothesis) :
    (fun X : ℕ => ((((Finset.Icc 2 X ×ˢ Finset.Icc 2 X).filter fun p : ℕ × ℕ =>
        p.2 ≤ p.1 ∧ π p.1 + π p.2 < π (p.1 + p.2)).card : ℕ) : ℝ)) =O[atTop]
      fun X : ℕ => (X : ℝ) ^ (3 / 2 : ℝ) * Real.log X ^ 2 := by
  sorry

end Erdos855
