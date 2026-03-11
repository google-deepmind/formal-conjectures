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
# Erdős Problem 15

*Reference:* [erdosproblems.com/15](https://www.erdosproblems.com/15)

Is the alternating series $\sum_{n=1}^{\infty} (-1)^n \cdot n / p_n$ convergent, where $p_n$
denotes the $n$-th prime? Tao [Ta23] has proved convergence assuming a strong form of the
Hardy–Littlewood prime tuples conjecture.

Erdős also conjectured [Er98]:
- $\sum (-1)^n / (n(p_{n+1} - p_n))$ converges,
- $\sum (-1)^n / (p_{n+1} - p_n)$ diverges,
- $\sum (-1)^n / (n(p_{n+1} - p_n)(\log\log n)^c)$ converges for all $c > 0$.

Weisenberg showed that Zhang's result [Zh14] on bounded prime gaps implies the second variant
diverges, and argued the series is unbounded in at least one direction under Hardy–Littlewood.
Erdős–Nathanson and Sawhney proved absolute convergence of the third variant for $c > 2$.

[Er97] Erdős, P., _Some of my new and almost new problems and results in combinatorial
number theory_ (1997).

[Er97e] Erdős, P., _Some problems and results on combinatorial number theory_ (1997).

[Er98] Erdős, P., _Some of my favourite problems which recently have been solved_,
Challenges for the 21st century (Singapore, 2000), 2001.

[Ta23] Tao, T., _Monotone non-decreasing sequences of the Euler totient function_,
arXiv:2309.02325 (2023).

[Zh14] Zhang, Y., _Bounded gaps between primes_. Ann. of Math. (2) **179** (2014), 1121–1174.
-/

open Filter

open scoped BigOperators Topology

namespace Erdos15

/--
Is it true that the alternating series
$$\sum_{n=1}^{\infty} (-1)^n \cdot \frac{n}{p_n}$$
converges, where $p_n$ denotes the $n$-th prime?

This is an open problem. Tao [Ta23] has proved convergence assuming a strong form
of the Hardy–Littlewood prime tuples conjecture.

We state convergence as: the sequence of partial sums
$$S_N = \sum_{n=1}^{N} (-1)^n \cdot \frac{n}{p_n}$$
converges to a real limit $L$.

Using 0-indexed `Nat.nth Nat.Prime`, the $n$-th term ($n : \mathbb{N}$, 0-indexed) is
$(-1)^{n+1} \cdot (n+1) / p_{n+1}$, corresponding to the 1-indexed mathematical term.
-/
@[category research open, AMS 11 40]
theorem erdos_15 : answer(sorry) ↔ ∃ L : ℝ,
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ (n + 1) * ((n + 1 : ℝ) / (Nat.nth Nat.Prime n : ℝ)))
      atTop (nhds L) := by
  sorry

/--
**Variant 1** [Er98]: Does the alternating series
$$\sum_{n=1}^{\infty} (-1)^n \cdot \frac{1}{n(p_{n+1} - p_n)}$$
converge? Erdős conjectured it does.

We use 0-indexed `primeGap n = p_{n+1} - p_n` and shift the summation index by 1.
The sum starts at $n = 1$ (0-indexed) to avoid division by zero at $n = 0$.
-/
@[category research open, AMS 11 40]
theorem erdos_15.variants.convergence_gap_weighted : answer(sorry) ↔ ∃ L : ℝ,
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ (n + 1) * (1 / ((n + 1 : ℝ) * (primeGap (n + 1) : ℝ))))
      atTop (nhds L) := by
  sorry

/--
**Variant 2** [Er98]: Does the alternating series
$$\sum_{n=1}^{\infty} (-1)^n \cdot \frac{1}{p_{n+1} - p_n}$$
diverge? Erdős conjectured it does.

Weisenberg showed that Zhang's result [Zh14] on bounded prime gaps implies this series diverges.
-/
@[category research open, AMS 11 40]
theorem erdos_15.variants.divergence_gap : answer(sorry) ↔ ¬∃ L : ℝ,
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ (n + 1) * (1 / (primeGap (n + 1) : ℝ)))
      atTop (nhds L) := by
  sorry

/--
**Variant 3** [Er98]: Does the alternating series
$$\sum_{n=1}^{\infty} (-1)^n \cdot \frac{1}{n(p_{n+1} - p_n)(\log\log n)^c}$$
converge for all $c > 0$? Erdős conjectured it does.

Erdős–Nathanson and Sawhney proved absolute convergence for $c > 2$.
The sum starts at $n = 3$ (0-indexed $n = 2$) to ensure $\log\log n > 0$.
-/
@[category research open, AMS 11 40]
theorem erdos_15.variants.convergence_loglog : answer(sorry) ↔
    ∀ c : ℝ, c > 0 → ∃ L : ℝ,
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ (n + 3) *
          (1 / ((n + 3 : ℝ) * (primeGap (n + 3) : ℝ) * (Real.log (Real.log (n + 3 : ℝ))) ^ c)))
      atTop (nhds L) := by
  sorry

end Erdos15
