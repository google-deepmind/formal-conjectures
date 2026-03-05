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
# Erdős Problem 378

*Reference:* [erdosproblems.com/378](https://www.erdosproblems.com/378)

For every $r \ge 0$, the natural density of the set of integers $n$ for which $\binom{n}{k}$
is squarefree for at least $r$ values of $1 \le k < n$ exists and is positive.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[GrRa96] Granville, A. and Ramaré, O., *Explicit bounds on exponential sums and the scarcity of
squarefree binomial coefficients*. Mathematika 43 (1996), 73-107.
-/

open Classical Filter

namespace Erdos378

/-- The upper density of $A \subseteq \mathbb{N}$. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/-- The lower density of $A \subseteq \mathbb{N}$. -/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/-- A set of natural numbers has natural density $d$. -/
def HasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  upperDensity A = d ∧ lowerDensity A = d

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

Resolved in the affirmative by the results of Granville and Ramaré [GrRa96], who show that for
each $m$, the density of the set of $n$ such that $\binom{n}{k}$ is squarefree for exactly
$2m + 2$ values of $k$ exists.
-/
@[category research solved, AMS 11]
theorem erdos_378 (r : ℕ) :
    ∃ d : ℝ, d > 0 ∧ HasNaturalDensity (squarefreeBinomAtLeast r) d := by
  sorry

end Erdos378
