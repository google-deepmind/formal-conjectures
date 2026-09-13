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

import FormalConjecturesUtil

/-!
# Erdős Problem 999

*Reference:* [erdosproblems.com/999](https://www.erdosproblems.com/999)
-/

open MeasureTheory Real

namespace Erdos999

/-- Infinitely many coprime approximations $|\alpha-p/q|<f(q)/q$. -/
def InfiniteApproximations (α : ℝ) (f : ℕ → ℕ) : Prop :=
  { q : ℕ | 0 < q ∧ ∃ p : ℕ, Nat.Coprime p q ∧ |α - (p : ℝ) / q| < f q / q }.Infinite

/--
For any function $f:\mathbb{N}\to \mathbb{N}$ the property that, for almost all $\alpha$
$$
\left\lvert \alpha-\frac{p}{q}\right\rvert < \frac{f(q)}{q}
$$
has infinitely many solutions with $(p,q)=1$, is equivalent to
$$
\sum_{q\geq 1}\phi(q)\frac{f(q)}{q}=\infty.
$$
-/
@[category research solved, AMS 11]
theorem erdos_999 (f : ℕ → ℕ) :
    (∀ᵐ α : ℝ, InfiniteApproximations α f) ↔
      ¬ Summable fun q : ℕ ↦ (q.totient : ℝ) * f q / q := by
  sorry

end Erdos999
