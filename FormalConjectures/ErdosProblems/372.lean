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
# Erdős Problem 372

*Reference:* [erdosproblems.com/372](https://www.erdosproblems.com/372)

Let $P(n)$ denote the largest prime factor of $n$. There are infinitely many $n$
such that $P(n) > P(n+1) > P(n+2)$.

Conjectured by Erdős and Pomerance [ErPo78], who proved the analogous result
for $P(n) < P(n+1) < P(n+2)$. Solved by Balog [Ba01], who proved that this is
true for $\gg \sqrt{x}$ many $n \leq x$ (for all large $x$). Balog suggests the natural
conjecture that the density of such $n$ is $1/6$.

[ErPo78] Erdős, P. and Pomerance, C., _On the largest prime factors of n and n+1_,
Aequationes Math. 17 (1978), 311-321.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathematique (1980).

[Er85c] Erdős, P., _Some problems and results on combinatorial number theory_ (1985).

[Ba01] Balog, A., _On triplets with descending largest prime factors_, Studia Sci.
Math. Hungar. 38 (2001), 45-50.
-/

namespace Erdos372

/-- The largest prime factor of a natural number $n$. Returns $0$ if $n \leq 1$. -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  n.factorization.support.sup id

/--
Erdős Problem 372 [ErPo78] [ErGr80] [Er85c]:

There are infinitely many $n$ such that $P(n) > P(n+1) > P(n+2)$, where
$P(n)$ denotes the largest prime factor of $n$.
-/
@[category research solved, AMS 11]
theorem erdos_372 :
    Set.Infinite {n : ℕ |
      largestPrimeFactor n > largestPrimeFactor (n + 1) ∧
      largestPrimeFactor (n + 1) > largestPrimeFactor (n + 2)} := by
  sorry

end Erdos372
