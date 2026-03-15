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
# Erdős Problem 83

*Reference:* [erdosproblems.com/83](https://www.erdosproblems.com/83)

If $\mathcal{F}$ is a family of $2n$-element subsets of $[4n]$ with pairwise intersections
of size $\geq 2$, then $|\mathcal{F}| \leq \frac{1}{2}(\binom{4n}{2n} - \binom{2n}{n}^2)$.
Conjectured by Erdős, Ko, and Rado [ErKoRa61], proved by Ahlswede and Khachatrian [AhKh97].
This problem carried a \$500 reward.

The extremal family consists of all subsets of $[4n]$ of size $2n$ containing at least $n+1$
elements from $[2n]$.

OEIS: [A071799](https://oeis.org/A071799), [A387635](https://oeis.org/A387635).

[ErKoRa61] Erdős, P., Ko, C., and Rado, R., _Intersection theorems for systems of
finite sets_. Quart. J. Math. Oxford Ser. (2) 12 (1961), 313-320.

[AhKh97] Ahlswede, R. and Khachatrian, L.H., _The complete intersection theorem for
systems of finite sets_. European J. Combin. 18 (1997), 125-136.

[Er71] Erdős, P., _Topics in combinatorial analysis_ (1971).

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
467-478.

[Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
Eureka (1992), 44-48.

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Combinatorics '94 (Catania), Congressus Numerantium 107 (1995).
-/

open Finset

namespace Erdos83

/--
Suppose that we have a family $\mathcal{F}$ of subsets of $[4n]$ such that $|A| = 2n$ for all
$A \in \mathcal{F}$ and for every $A, B \in \mathcal{F}$ we have $|A \cap B| \geq 2$. Then
$$
  |\mathcal{F}| \leq \frac{1}{2}\left(\binom{4n}{2n} - \binom{2n}{n}^2\right).
$$

This was conjectured by Erdős, Ko, and Rado [ErKoRa61], and proved by Ahlswede and
Khachatrian [AhKh97].
-/
@[category research solved, AMS 5]
theorem erdos_83 :
    ∀ n : ℕ, 0 < n →
    ∀ F : Finset (Finset (Fin (4 * n))),
      (∀ A ∈ F, A.card = 2 * n) →
      (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≥ 2) →
      F.card ≤ (Nat.choose (4 * n) (2 * n) - Nat.choose (2 * n) n ^ 2) / 2 := by
  sorry

end Erdos83
