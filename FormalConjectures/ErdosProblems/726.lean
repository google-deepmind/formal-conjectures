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
# Erdős Problem 726

*Reference:* [erdosproblems.com/726](https://www.erdosproblems.com/726)

A conjecture of Erdős, Graham, Ruzsa, and Straus.

[EGRS75] Erdős, P., Graham, R., Ruzsa, I., and Straus, E.
-/

open Filter Nat

open scoped Topology Real

namespace Erdos726

/-- The weighted sum of $1/p$ over primes $p \le n$ for which $n \bmod p$ lies in $(p/2, p)$,
i.e., $2 \cdot (n \bmod p) > p$. This captures the condition $n \equiv r \pmod{p}$ for some
integer $r$ with $p/2 < r < p$. -/
noncomputable def erdos726Sum (n : ℕ) : ℝ :=
  ((Finset.range (n + 1)).filter Nat.Prime).sum
    (fun p => if 2 * (n % p) > p then (1 : ℝ) / (p : ℝ) else 0)

/--
Erdős Problem 726 [EGRS75]:

As $n \to \infty$,
$$\sum_{\substack{p \le n \\ p \text{ prime}}} \mathbf{1}_{n \in (p/2, p) \pmod{p}} \cdot
\frac{1}{p} \sim \frac{\log \log n}{2}.$$

Stated as: the ratio of the sum to $(\log \log n)/2$ tends to $1$.
-/
@[category research open, AMS 11]
theorem erdos_726 :
    Tendsto (fun n : ℕ => erdos726Sum n / (Real.log (Real.log (n : ℝ)) / 2))
      atTop (nhds 1) := by
  sorry

end Erdos726
