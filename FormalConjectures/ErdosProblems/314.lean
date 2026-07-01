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
# Erdős Problem 314

*References:*
- [erdosproblems.com/314](https://www.erdosproblems.com/314)
- [LiSt24] J. Lim and Steinerberger, S., *On differences of two harmonic numbers*.
  arXiv:2405.11354 (2024).
-/

open Filter

namespace Erdos314

/-- The block harmonic sum $\sum_{n\leq k\leq m}\frac{1}{k}$. -/
noncomputable def harmonicSum (n m : ℕ) : ℝ := ∑ k ∈ Finset.Icc n m, (1 : ℝ) / k

/-- `mMin n` is the minimal `m` such that $\sum_{n\leq k\leq m}\frac{1}{k}\geq 1$; such an `m`
exists for `n ≥ 1` since the harmonic series diverges. -/
noncomputable def mMin (n : ℕ) : ℕ := sInf {m | 1 ≤ harmonicSum n m}

/-- $\epsilon(n) = \sum_{n\leq k\leq m}\frac{1}{k}-1$, the overshoot of the minimal block sum
reaching $1$. -/
noncomputable def epsilon (n : ℕ) : ℝ := harmonicSum n (mMin n) - 1

/--
Let $n\geq 1$ and let $m$ be minimal such that $\sum_{n\leq k\leq m}\frac{1}{k}\geq 1$. We define
\[\epsilon(n) = \sum_{n\leq k\leq m}\frac{1}{k}-1.\]
How small can $\epsilon(n)$ be? Is it true that
\[\liminf n^2\epsilon(n)=0?\]

This is true, and shown by Lim and Steinerberger [LiSt24], who further proved that, for any
$\delta>0$, there exist infinitely many $n$ and $m$ such that
\[n^2\left\lvert \sum_{n\leq k\leq m}\frac{1}{k}-1\right\rvert\ll \frac{1}{(\log n)^{5/4-\delta}}.\]
Erdős and Graham (and also Lim and Steinerberger) believe that the exponent of $2$ is best
possible here, in that $\liminf \epsilon(n) n^{2+\delta}=\infty$ for all $\delta>0$.
-/
@[category research solved, AMS 11 40,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos314.lean"]
theorem erdos_314 : answer(True) ↔
    atTop.liminf (fun n : ℕ => (n : ℝ) ^ 2 * epsilon n) = 0 := by
  sorry

end Erdos314
