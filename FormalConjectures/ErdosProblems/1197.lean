/-
Copyright 2025 The Formal Conjectures Authors.

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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1197

*References:*
- [erdosproblems.com/1197](https://www.erdosproblems.com/1197)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [BuMa99] Buczolich, Zoltán and Mauldin, R. Daniel, *On the convergence of
  $\sum^\infty_{n=1}f(nx)$ for measurable functions*. Mathematika (1999), 337--341.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Pointwise

namespace Erdos1197

/--
Let $E\subset (0,\infty)$ be a set of positive measure. Is it true that, for almost all $x>0$,
for all sufficiently large (depending on $x$) integers $n$ there exists an integer $r\geq 1$ such
that $nx\in r\cdot E$?

A problem of Haight, who constructed a set $E\subset (0,\infty)$ of infinite measure such that,
for all $x\in E$, $x\not\in r\cdot E$ if $r\geq 2$, and also for all $x>0$, if $n$ is large enough
then $nx\not\in E$ (see [1195](https://www.erdosproblems.com/1195)).

This is trivially true if $E$ contains an interval $(a,b)$ with $a<b$, since for any $x>0$, for
all large $n$, the interval $(\frac{nx}{b},\frac{nx}{a})$ has length $>1$ so contains at least
one integer $r\geq 1$.

Buczolich and Mauldin [BuMa99] proved that there exists an open set $E\subset (0,\infty)$ and two
intervals $I,J\subset [1/2,1)$ such that, for all $x\in I$, $x\in \frac{1}{n}\cdot E$ for
infinitely many $n\geq 1$, and for almost all $x\in J$, $x\not\in \frac{1}{n}\cdot E$ for all
sufficiently large (depending on $x$) $n$.

This was solved in the negative by ebarschkis in the comments, who constructed a counterexample
using a variant of the Buczolich-Mauldin construction.
-/
@[category research solved, AMS 11 28, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1197.lean#L705"]
theorem erdos_1197 : answer(False) ↔ ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioi 0 → 0 < volume E →
    ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ᶠ n : ℕ in atTop,
      ∃ r : ℕ, 1 ≤ r ∧ (n : ℝ) * x ∈ (r : ℝ) • E := by
  sorry

end Erdos1197
