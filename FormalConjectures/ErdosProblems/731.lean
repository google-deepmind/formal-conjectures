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
# Erdős Problem 731

For almost all $n$, the least integer $m \geq 2$ not dividing $\binom{2n}{n}$ satisfies
$m = \exp((\log n)^{1/2 + o(1)})$. The open problem asks to find a precise closed-form
function $f(n)$ such that $m \sim f(n)$ for almost all $n$.

*Reference:* [erdosproblems.com/731](https://www.erdosproblems.com/731)

[EGRS75] Erdős, P., Graham, R. L., Ruzsa, I. Z., and Straus, E. G.,
_On the prime factors of $\binom{2n}{n}$_. Mathematics of Computation **29** (1975), 83–92.

- [A006197](https://oeis.org/A006197)
-/

open Finset Filter Real

open scoped Topology

namespace Erdos731

/-- The least integer $m \geq 2$ that does not divide $\binom{2n}{n}$. -/
noncomputable def leastNonDivisorCentralBinom (n : ℕ) : ℕ :=
  sInf {m : ℕ | 2 ≤ m ∧ ¬(m ∣ n.centralBinom)}

/--
Erdős Problem 731 [EGRS75]:

For almost all $n$, the least $m \geq 2$ not dividing $\binom{2n}{n}$ satisfies
$$m = \exp((\log n)^{1/2 + o(1)}),$$
i.e., for every $\varepsilon > 0$, the natural density of integers $n$ where the
least non-divisor of $\binom{2n}{n}$ falls outside the interval
$$[\exp((\log n)^{1/2 - \varepsilon}),\, \exp((\log n)^{1/2 + \varepsilon})]$$
is zero.

The open problem asks to find a precise closed-form function $f(n)$ such
that $m \sim f(n)$ for almost all $n$. This theorem formalizes the known
asymptotic from [EGRS75]; the full open problem (identifying $f$) remains open.
-/
@[category research open, AMS 5 11]
theorem erdos_731 (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun x : ℕ =>
      (((Finset.Icc 1 x).filter (fun n : ℕ =>
        let m : ℝ := (leastNonDivisorCentralBinom n : ℝ)
        ¬(exp ((log (↑n : ℝ)) ^ ((1 : ℝ) / 2 - ε)) ≤ m ∧
          m ≤ exp ((log (↑n : ℝ)) ^ ((1 : ℝ) / 2 + ε))))).card : ℝ) / (↑x : ℝ))
      atTop (nhds 0) := by
  sorry

end Erdos731
