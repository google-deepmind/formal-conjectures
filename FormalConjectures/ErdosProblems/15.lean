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
denotes the $n$-th prime? Tao has proved convergence assuming a strong form of the
Hardy–Littlewood prime tuples conjecture.
-/

open Filter

open scoped BigOperators Topology

namespace Erdos15

/--
Is it true that the alternating series
$$\sum_{n=1}^{\infty} (-1)^n \cdot \frac{n}{p_n}$$
converges, where $p_n$ denotes the $n$-th prime?

This is an open problem. Tao has proved convergence assuming a strong form
of the Hardy–Littlewood prime tuples conjecture.

We state convergence as: the sequence of partial sums
$$S_N = \sum_{n=1}^{N} (-1)^n \cdot \frac{n}{p_n}$$
converges to a real limit $L$.

Using 0-indexed `Nat.nth Nat.Prime`, the $n$-th term ($n : \mathbb{N}$, 0-indexed) is
$(-1)^{n+1} \cdot (n+1) / p_{n+1}$,
which corresponds to the 1-indexed term $(-1)^{n+1} \cdot (n+1)/p_{n+1}$.
-/
@[category research open, AMS 11 40]
theorem erdos_15 : answer(sorry) ↔ ∃ L : ℝ,
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ (n + 1) * ((n + 1 : ℝ) / (Nat.nth Nat.Prime n : ℝ)))
      atTop (nhds L) := by
  sorry

end Erdos15
