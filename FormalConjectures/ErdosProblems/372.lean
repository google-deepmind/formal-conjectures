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
import FormalConjecturesForMathlib.Data.Nat.MaxPrimeFac

/-!
# Erdős Problem 372

*Reference:* [erdosproblems.com/372](https://www.erdosproblems.com/372)

Let $P(n)$ denote the largest prime factor of $n$. There are infinitely many $n$
such that $P(n) > P(n+1) > P(n+2)$.

Conjectured by Erdős and Pomerance [ErPo78], who proved the analogous result
for $P(n) < P(n+1) < P(n+2)$. Solved by Balog [Ba01], who proved that this is
true for $\gg \sqrt{x}$ many $n \leq x$ (for all large $x$). Balog suggests the natural
conjecture that the density of such $n$ is $1/6$. A generalised form of this
conjecture was presented by De Koninck and Doyon [DeDo11].

OEIS: [A071870](https://oeis.org/A071870)

[ErPo78] Erdős, P. and Pomerance, C., _On the largest prime factors of n and n+1_,
Aequationes Math. **17** (1978), 311-321.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathematique (1980).

[Er85c] Erdős, P., _Some problems and results on combinatorial number theory_ (1985).

[Ba01] Balog, A., _On triplets with descending largest prime factors_, Studia Sci.
Math. Hungar. **38** (2001), 45-50.

[DeDo11] De Koninck, J.-M. and Doyon, N., _On the distance between smooth numbers_,
Integers **11** (2011), A25.
-/

namespace Erdos372

/--
Erdős Problem 372 [ErPo78] [ErGr80] [Er85c]:

There are infinitely many $n$ such that $P(n) > P(n+1) > P(n+2)$, where
$P(n)$ denotes the largest prime factor of $n$.
-/
@[category research solved, AMS 11]
theorem erdos_372 :
    Set.Infinite {n : ℕ |
      n.maxPrimeFac > (n + 1).maxPrimeFac ∧
      (n + 1).maxPrimeFac > (n + 2).maxPrimeFac} := by
  sorry

end Erdos372
