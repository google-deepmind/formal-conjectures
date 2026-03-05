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
# Erdős Problem 955

If $A \subseteq \mathbb{N}$ has natural density zero, must the preimage $s^{-1}(A)$ also have
natural density zero, where $s(n)$ denotes the sum of proper divisors of $n$?

*Reference:* [erdosproblems.com/955](https://www.erdosproblems.com/955)

[EGPS90] Erdős, P., Granville, A., Pomerance, C., and Spiro, C., _On the normal behavior of
the iterates of some arithmetic functions_. Analytic number theory (Allerton Park, IL, 1989),
Progr. Math., 85 (1990), 165-204.
-/

open scoped Classical

namespace Erdos955

/-- The sum of proper divisors function $s(n) = \sum_{d \mid n,\, d < n} d$. -/
def sumProperDivisors (n : ℕ) : ℕ := n.properDivisors.sum id

/-- A set $A \subseteq \mathbb{N}$ has natural density zero if for every $\varepsilon > 0$,
there exists $N$ such that for all $x \geq N$, the proportion of elements of $A$
below $x$ is less than $\varepsilon$. -/
def HasNaturalDensityZero (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ x : ℕ, x ≥ N →
    ((Finset.filter (· ∈ A) (Finset.range x)).card : ℝ) / (x : ℝ) < ε

/--
**Erdős Problem 955** [EGPS90]:

If $A \subseteq \mathbb{N}$ has natural density zero, then so does
$s^{-1}(A) = \{n \in \mathbb{N} : s(n) \in A\}$, where $s$ is the sum of proper divisors
function.
-/
@[category research open, AMS 11]
theorem erdos_955 (A : Set ℕ) (hA : HasNaturalDensityZero A) :
    HasNaturalDensityZero {n : ℕ | sumProperDivisors n ∈ A} := by
  sorry

end Erdos955
