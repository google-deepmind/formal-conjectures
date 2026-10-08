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
import FormalConjecturesForMathlib.Combinatorics.AP.Basic

open scoped Pointwise

/-!
# Ben Green's Open Problem 30

Given a set $A \subset \mathbb{Z}$ with $D(A) \leq K$, find a large structured subset $A' \subset A$
which 'obviously' has $D(A') \leq K + \varepsilon$, with $D(A) := |A - A|/|A|$.

*References:*
- [Gr24] [Ben Green's Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.30)
- [EGM13] Eberhard, Sean, Ben Green, and Freddie Manners. "Sets of integers with no large sum-free
  subset." Annals of Mathematics (2014): 621-652.
-/

namespace Green30

-- TODO(jgd): Formalize the full conjecture (need to clarify the terms "large", "structured", and "obviously")

/-- Difference-set doubling ratio $D(A) = |A - A| / |A|$. -/
noncomputable abbrev D (A : Finset ℤ) : ℝ :=
  ((A - A).card : ℝ) / (A.card : ℝ)

/--
An example to help interpret the conjecture.

If $|A - A| \leq (4 - \varepsilon)|A|$, then there is a progression $P$ of length
$\gg_\varepsilon |A|$ on which $A$ has density $> 1/2$. Then $A' := A \cap P$ "obviously" has
$D(A') \leq 4$ [Gr24].
-/
@[category research solved, AMS 05 11]
theorem green_30.example :
    ∀ (ε : ℝ), ε > 0 →
      ∃ (k : ℝ), k > 0 ∧
        ∀ A : Finset ℤ, A.Nonempty →
          D A ≤ 4 - ε →
          let A' : Finset ℤ := answer(sorry)
          ∃ P : Finset ℤ, (P : Set ℤ).IsAPOfLength P.card ∧
            A' = A ∩ P ∧
            k * A.card ≤ P.card ∧
            P.card < 2 * A'.card ∧
            D A' ≤ 4 := by
  sorry

/--
Let $\varepsilon > 0$. Suppose that $A$ is a finite set of integers such that
$|A − A| \leq (4 − \varepsilon)|A|$. Then there is an arithmetic progression $P \subset \mathbb{Z}$
of length $\gg_\varepsilon |A|$ on which the density of $A$ is at least $1/2 + c\varepsilon$.
[EGM13, Theorem 6.4]
-/
@[category research solved, AMS 05 11]
theorem green_30.variants.EGM13 :
    ∃ c : ℝ, c > 0 ∧
      ∀ (ε : ℝ), ε > 0 →
        ∃ k : ℝ, k > 0 ∧
          ∀ A : Finset ℤ, A.Nonempty →
            D A ≤ 4 - ε →
            ∃ P : Finset ℤ, (P : Set ℤ).IsAPOfLength P.card ∧
              k * A.card ≤ P.card ∧
              (1 / 2 + c * ε) * P.card ≤ ((A ∩ P).card : ℝ) := by
  sorry

end Green30
