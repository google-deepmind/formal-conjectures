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
# Erdős Problem 46

*Reference:* [erdosproblems.com/46](https://www.erdosproblems.com/46)

For every finite colouring of the integers $\geq 2$, there exists a monochromatic finite
set whose reciprocals sum to $1$. Proved by Croot [Cr03].

See also: Problem #298.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980), p. 36.

[Cr03] Croot, E.S., _On a coloring conjecture about unit fractions_, Annals of Mathematics
**157** (2003), 545–556.
-/

open Finset BigOperators

namespace Erdos46

/-- The reciprocal sum $\sum_{n \in A} 1/n$ of a finite set of natural numbers. -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / (n : ℚ)

/--
For every $k$-colouring (with $k \ge 2$) of the positive integers $\ge 2$, there exists a
monochromatic finite set $\{n_1, \ldots, n_m\}$ with $2 \le n_1 < \cdots < n_m$ whose
reciprocals sum to $1$, i.e. $\sum 1/n_i = 1$.

Proved by Croot [Cr03]. Originally posed by Erdős and Graham [ErGr80].
-/
@[category research solved, AMS 5 11]
theorem erdos_46 : answer(True) ↔
    ∀ k : ℕ, k ≥ 2 →
    ∀ (c : ℕ → Fin k),
      ∃ S : Finset ℕ, S.Nonempty ∧
        (∀ n ∈ S, n ≥ 2) ∧
        (∃ j : Fin k, ∀ n ∈ S, c n = j) ∧
        reciprocalSum S = 1 := by
  sorry

/--
Generalization of `erdos_46` to arbitrary positive rationals: for every $k$-colouring
(with $k \ge 2$) of the positive integers $\ge 2$ and every positive rational $q$, there
exists a monochromatic finite subset whose reciprocals sum to $q$.

This follows from the unit case by considering induced colorings on $\{n/b : b \mid n\}$.
Originally posed by Erdős and Graham [ErGr80].
-/
@[category research solved, AMS 5 11]
theorem erdos_46_rational_generalization :
    ∀ k : ℕ, k ≥ 2 →
    ∀ (q : ℚ), 0 < q →
    ∀ (c : ℕ → Fin k),
      ∃ S : Finset ℕ, S.Nonempty ∧
        (∀ n ∈ S, n ≥ 2) ∧
        (∃ j : Fin k, ∀ n ∈ S, c n = j) ∧
        reciprocalSum S = q := by
  sorry

end Erdos46
