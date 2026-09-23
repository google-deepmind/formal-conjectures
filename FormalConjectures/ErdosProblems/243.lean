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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 243

*Reference:* [erdosproblems.com/243](https://www.erdosproblems.com/243)
-/

@[expose] public section

open Filter

open scoped Topology

namespace Erdos243

/--
Let $a_1 < a_2 < \dots$ be a sequence of integers such that
$\lim_{n\to\infty} \frac{a_n}{a_{n-1}^2} = 1$ and $\sum \frac{1}{a_n} \in \mathbb{Q}$.

Then, for all sufficiently large $n \ge 1$, $a_n = a_{n-1}^2 - a_{n-1} + 1$.
-/
@[category research open, AMS 40]
theorem erdos_243 (a : ℕ → ℕ) (ha₀ : StrictMono a)
    (ha₁ : Tendsto (fun n ↦ (a n : ℝ) / a (n - 1) ^ 2) atTop (𝓝 1))
    (ha₂ : Summable ((1 : ℚ) / a ·)) :
      ∀ᶠ n in atTop, a n = a (n - 1) ^ 2 - a (n - 1) + 1 := by
  sorry

/--
Let $(a_n)_{n\geq 0}$ be a strictly increasing sequence of positive integers. If
\[
  \frac{a_n^2}{a_{n+1}}=1+\frac{3}{n}+o(n^{-3}),
\]
then its reciprocal sum is irrational.

This is the zero-indexed formal version of the cubic-rate theorem in Will Cook,
*Cubic-Rate Irrationality and Reciprocal-Tail Rigidity*, Theorem 16. The rate keeps
the same index on both sides; shifting $n$ would change its lower-order terms.
This variant does not settle the unrestricted Erdős problem above.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/lean/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L70-L77"]
theorem erdos_243.variants.cubic_rate (a : ℕ → ℕ)
    (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ)))) atTop (𝓝 0)) :
    Irrational (∑' n : ℕ, 1 / (a n : ℝ)) := by
  sorry

end Erdos243
