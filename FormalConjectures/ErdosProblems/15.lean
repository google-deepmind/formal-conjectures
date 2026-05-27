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
# Erdős Problem 15: Convergence of Series with Primes

*Reference:* [erdosproblems.com/15](https://www.erdosproblems.com/15)
-/

namespace Erdos15

open Filter Topology

/--
Is it true that $\sum_{n=1}^\infty(-1)^n\frac{n}{p_n}$ converges,
where $p_n$ is the sequence of primes?

Note: In the problem statement, $p_n$ is the $n$-th prime, indexed such that $p_1=2, p_2=3, \ldots$.
We 0-index here to reflect how Nat.nth works.
-/
@[category research open, AMS 11]
theorem erdos_15 : answer(sorry) ↔
    Summable (fun k : ℕ => (-1 : ℚ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime)) := by
  sorry


-- TODO: add the other statements from the additional material


end Erdos15
