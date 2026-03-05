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
# Erdős Problem 461

Erdős and Graham asked whether the number of distinct smooth components among consecutive
integers grows linearly: specifically, whether $f(n,t) \gg t$ uniformly for all $n$ and $t$.

*Reference:* [erdosproblems.com/461](https://www.erdosproblems.com/461)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset BigOperators

namespace Erdos461

/-- The $t$-smooth component of $n$: the product of $p^{v_p(n)}$ over all
    primes $p < t$ dividing $n$. -/
noncomputable def smoothComponent (t n : ℕ) : ℕ :=
  (n.factorization.support.filter (· < t)).prod
    (fun p => p ^ n.factorization p)

/-- $f(n, t)$ counts the number of distinct values of the $t$-smooth component
    of $m$ for $m \in \{n+1, \ldots, n+t\}$. -/
noncomputable def f (n t : ℕ) : ℕ :=
  ((Finset.Icc (n + 1) (n + t)).image (smoothComponent t)).card

/--
Erdős Problem 461 [ErGr80, p.92]:

Is it true that $f(n,t) \gg t$ uniformly for all $n$ and $t$, where $f(n,t)$
counts the number of distinct $t$-smooth components among $\{n+1, \ldots, n+t\}$?
-/
@[category research open, AMS 11]
theorem erdos_461 :
    answer(sorry) ↔
      ∃ c : ℝ, c > 0 ∧ ∀ n t : ℕ, 0 < t →
        (f n t : ℝ) ≥ c * (t : ℝ) := by
  sorry

end Erdos461
