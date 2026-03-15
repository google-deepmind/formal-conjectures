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
# Erdős Problem 1120

For a monic polynomial of degree $n$ with all roots in the unit disk, consider the lemniscate set
$E = \{z : |f(z)| \leq 1\}$. Erdős conjectured that the worst-case shortest path length in $E$
from the origin to the unit circle tends to infinity with $n$.

See also Erdős Problem 1041 (paths connecting roots within lemniscate sets).

*Reference:* [erdosproblems.com/1120](https://www.erdosproblems.com/1120)

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_ (1974), 155–180.
-/

open Complex Polynomial Set

namespace Erdos1120

/-- The lemniscate (sublevel) set of a polynomial $f$: $\{z \in \mathbb{C} : \|f(z)\| \leq 1\}$. -/
noncomputable def lemniscateSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}

/--
Erdős Problem 1120 [Ha74, Problem 4.22]:

Let $f \in \mathbb{C}[z]$ be a monic polynomial of degree $n$, all of whose roots satisfy
$|z| \leq 1$. Let $E = \{z : |f(z)| \leq 1\}$. The worst-case shortest length of a path in $E$
joining $z = 0$ to $|z| = 1$ tends to infinity with $n$.

Erdős wrote "presumably this tends to infinity with $n$, but not too fast."
The trivial lower bound is $1$ (achieved by $f(z) = z^n$). Clunie and Netanyahu
showed that a path always exists joining $z = 0$ to $|z| = 1$ in $E$.

Formally: for every $C > 0$, there exists $N$ such that for all $n \geq N$, there exists a
monic polynomial $f$ of degree $n$ with all roots in the closed unit disk, such that
every continuous path $\gamma : [0,1] \to E$ from $0$ to the unit circle has arc length $\geq C$.
-/
@[category research open, AMS 30]
theorem erdos_1120 :
    ∀ C : ℝ, C > 0 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ f : Polynomial ℂ, f.Monic ∧ f.natDegree = n ∧
      (∀ z ∈ f.roots, ‖z‖ ≤ 1) ∧
      ∀ γ : ℝ → ℂ, Continuous γ →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ lemniscateSet f) →
        γ 0 = 0 →
        ‖γ 1‖ = 1 →
        ENNReal.ofReal C ≤ eVariationOn γ (Icc (0 : ℝ) 1) := by
  sorry

end Erdos1120
