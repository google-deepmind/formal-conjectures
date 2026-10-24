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
Let $(a_n)_{n\ge 0}$ be a strictly increasing sequence of positive integers,
and let $\lambda>1$ be a real number that is not an integer. If
$$
  \frac{a_n^2}{a_{n+1}}=1+\frac{\lambda}{n}+o(n^{-\lambda}),
$$
then $\sum_{n\ge 0}1/a_n$ is irrational. Convergence of the series follows
from these hypotheses. The rate uses the original index on both sides.

This is the zero-indexed formal version of the nonintegral regular-rate theorem
(Theorem 2.2) in W. Cook,
*Reciprocal Sums and the Sylvester Recurrence: Further Results and Proofs*:
https://github.com/wcook04/plectis-erdos/blob/6db987f4a843ae40ab07ac782ef0cca1a95815c1/paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L154-L162
The rational-tail coordinates follow J. Koizumi, *Irrationality of the reciprocal
sum of doubly exponential sequences*, Lemma 4:
https://math.colgate.edu/~integers/aa28/aa28.pdf
The unrestricted Erdős problem above remains open.
-/
@[category research solved, AMS 11 40, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-erdos-lean/blob/71a2bc9f74f8650d7287581f799ba998fe26e60f/verification/FC243NonintegralRateCurrent/FCNonintegralRateSolutions.lean#L13-L21"]
theorem erdos_243.variants.nonintegral_regular_rate
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (l : ℝ) (hl : 1 < l) (hnonint : ∀ d : ℕ, l ≠ (d : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ l *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + l / (n : ℝ))))
      atTop (nhds 0)) :
    Irrational (∑' n : ℕ, 1 / (a n : ℝ)) := by
  sorry

end Erdos243
