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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 378

*Reference:* [erdosproblems.com/378](https://www.erdosproblems.com/378)

For every $r \ge 0$, the natural density of the set of integers $n$ for which $\binom{n}{k}$
is squarefree for at least $r$ values of $1 \le k < n$ exists and is positive.

As noted by Aggarwal and Cambie, this is resolved by Granville and Ramaré [GrRa96].

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[GrRa96] Granville, A. and Ramaré, O., *Explicit bounds on exponential sums and the scarcity of
squarefree binomial coefficients*. Mathematika 43 (1996), 73-107.
-/

open Classical Filter

namespace Erdos378

/-- The number of values $k$ with $1 \le k < n$ such that $\binom{n}{k}$ is squarefree. -/
noncomputable def squarefreeBinomCount (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun k => 0 < k ∧ Squarefree (Nat.choose n k))).card

/-- The set of $n$ for which $\binom{n}{k}$ is squarefree for at least $r$ values of
$1 \le k < n$. -/
def squarefreeBinomAtLeast (r : ℕ) : Set ℕ :=
  {n : ℕ | r ≤ squarefreeBinomCount n}

/--
Erdős Problem 378 [ErGr80, p.72]:
For every $r \ge 0$, the natural density of the set of integers $n$ for which $\binom{n}{k}$
is squarefree for at least $r$ values of $1 \le k < n$ exists and is positive.

Resolved in the affirmative by the results of Granville and Ramaré [GrRa96], as noted by
Aggarwal and Cambie. Granville and Ramaré show that for each $m$, the density of the set of $n$
such that $\binom{n}{k}$ is squarefree for exactly $2m + 2$ values of $k$ exists.
-/
@[category research solved, AMS 11]
theorem erdos_378 (r : ℕ) :
    (squarefreeBinomAtLeast r).HasPosDensity := by
  sorry

/--
For each $m$, the natural density of the set of integers $n$ such that $\binom{n}{k}$ is
squarefree for exactly $2m + 2$ values of $1 \le k < n$ exists.

This is a stronger structural result shown by Granville and Ramaré [GrRa96], from which
`erdos_378` follows.
-/
@[category research solved, AMS 11]
theorem erdos_378_exact (m : ℕ) :
    ∃ d : ℝ, {n : ℕ | squarefreeBinomCount n = 2 * m + 2}.HasDensity d := by
  sorry

end Erdos378
