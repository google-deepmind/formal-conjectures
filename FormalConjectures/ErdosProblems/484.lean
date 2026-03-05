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
# Erdős Problem 484

There exists an absolute constant $c > 0$ such that, whenever $\{1, \ldots, N\}$ is
$k$-coloured (and $N$ is large enough depending on $k$), there are at least $cN$
integers representable as a monochromatic sum $a + b$ with $a \neq b$.

*Reference:* [erdosproblems.com/484](https://www.erdosproblems.com/484)

[ESS89] Erdős, P., Sárközy, A., and Sós, V. T., *On sum sets of Sidon sets*,
Journal of Number Theory (1989).
-/

open Finset

namespace Erdos484

/--
Erdős Problem 484 (a conjecture of Roth, proved by Erdős–Sárközy–Sós [ESS89]):

There exists an absolute constant $c > 0$ such that, whenever $\{1, \ldots, N\}$ is
$k$-coloured (and $N$ is large enough depending on $k$), there are at least $cN$
integers in $\{1, \ldots, N\}$ representable as a monochromatic sum, i.e., as $a + b$
where $a, b \in \{1, \ldots, N\}$ lie in the same colour class and $a \neq b$.

Erdős, Sárközy, and Sós proved this and showed that in fact at least
$N/2 - O(N^{1 - 1/2^{k+1}})$ even numbers are of this form.
-/
@[category research solved, AMS 5 11]
theorem erdos_484 :
    ∃ c : ℝ, 0 < c ∧
    ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ χ : ℕ → Fin k,
    ∃ S ⊆ Finset.Icc 1 N,
      (S.card : ℝ) ≥ c * (N : ℝ) ∧
      ∀ n ∈ S, ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N,
        a ≠ b ∧ χ a = χ b ∧ a + b = n := by
  sorry

end Erdos484
