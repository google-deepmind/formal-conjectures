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
# Erdős Problem 45

*Reference:* [erdosproblems.com/45](https://www.erdosproblems.com/45)

For every $k$-colouring of the divisors of $n$ (excluding $1$ and $n$), there is a
monochromatic subset whose reciprocals sum to $1$. Proved by Croot [Cr03].

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Combinatorics '94 (Catania), Congressus Numerantium **107** (1995).

[Er96b] Erdős, P., _Some problems I presented or planned to present in my short talk_.
Analytic number theory, Vol. 1 (Allerton Park, IL, 1995) (1996), 333–335.

[Cr03] Croot, E., _On a coloring conjecture about unit fractions_. Ann. of Math. (2)
**157** (2003), 545–556.

[Gu04] Guy, R., _Unsolved Problems in Number Theory_, 3rd ed. Springer, 2004, Problem B2.
-/

open Finset BigOperators

namespace Erdos45

/-- The reciprocal sum $\sum_{n \in A} 1/n$ of a finite set of natural numbers. -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / (n : ℚ)

/--
The set of divisors of $n$ strictly between $1$ and $n$:
$$D(n) = \{ d \in \mathbb{N} \mid d \mid n,\; 1 < d < n \}$$
-/
def middleDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => 1 < d ∧ d < n)

/--
Proved by Croot [Cr03]: for every $k \geq 2$, there exists a positive integer $n$ such that
for any $k$-colouring of the set $D(n) = \{d : d \mid n,\, 1 < d < n\}$ of divisors of $n$
(excluding $1$ and $n$ itself), there is a monochromatic subset $D' \subseteq D(n)$ whose
reciprocals sum to $1$:
$$\sum_{d \in D'} \frac{1}{d} = 1.$$

*Reference:* [Cr03]
-/
@[category research solved, AMS 5 11]
theorem erdos_45 :
    ∀ k : ℕ, k ≥ 2 →
      ∃ n : ℕ, ∀ (c : ℕ → Fin k),
        ∃ D' : Finset ℕ, D' ⊆ middleDivisors n ∧
          D'.Nonempty ∧
          (∃ j : Fin k, ∀ d ∈ D', c d = j) ∧
          reciprocalSum D' = 1 := by
  sorry

end Erdos45
