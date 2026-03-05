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
# Erdős Problem 175

*Reference:* [erdosproblems.com/175](https://www.erdosproblems.com/175)

Show that, for any $n \geq 5$, the binomial coefficient $\binom{2n}{n}$ is not squarefree.

It is easy to see that $4 \mid \binom{2n}{n}$ except when $n = 2^k$, and hence it suffices
to prove this when $n$ is a power of $2$.

Proved by Sárközy [Sa85] for all sufficiently large $n$, and independently by
Granville and Ramaré [GrRa96] and Velammal [Ve95] for all $n \geq 5$.

[Sa85] Sárközy, A., *On divisors of binomial coefficients, I*. J. Number Theory **20** (1985), 70-80.

[GrRa96] Granville, A. and Ramaré, O., *Explicit bounds on exponential sums and the scarcity of squarefree binomial coefficients*. Mathematika **43** (1996), 73-107.

[Ve95] Velammal, G., *Is the binomial coefficient $\binom{2n}{n}$ squarefree?*. Hardy-Ramanujan J. **18** (1995), 23-45.
-/

namespace Erdos175

/--
Erdős Problem 175 [Er79, ErGr80]:
For any $n \geq 5$, the central binomial coefficient $\binom{2n}{n}$ is not squarefree.
That is, there exists some prime $p$ such that $p^2$ divides $\binom{2n}{n}$.
-/
@[category research solved, AMS 11]
theorem erdos_175 :
    ∀ n : ℕ, 5 ≤ n → ¬Squarefree (Nat.choose (2 * n) n) := by
  sorry

end Erdos175
