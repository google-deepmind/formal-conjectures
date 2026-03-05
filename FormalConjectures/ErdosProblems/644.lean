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
# Erdős Problem 644

*Reference:* [erdosproblems.com/644](https://www.erdosproblems.com/644)

Let $f(k,r)$ be minimal such that if $A_1, A_2, \ldots$ is a family of sets,
all of size $k$, such that for every collection of $r$ of the $A_i$s there
is some pair $\{x,y\}$ which intersects all of the $A_j$, then there is some
set of size $f(k,r)$ which intersects all of the sets $A_i$.

Known results (Erdős, Fon-Der-Flaass, Kostochka, and Tuza [EFKT92]):
$f(k,3) = 2k$, $f(k,4) = \lfloor 3k/2 \rfloor$,
$f(k,5) = \lfloor 5k/4 \rfloor$, and $f(k,6) = k$.

[EFKT92] Erdős, P., Fon-Der-Flaass, D., Kostochka, A., and Tuza, Z.

[Er97d] Erdős, P.
-/

namespace Erdos644

/-- A family of sets is $k$-uniform: every set has exactly $k$ elements. -/
def IsKUniformFamily {ι : Type*} (F : ι → Finset ℕ) (k : ℕ) : Prop :=
  ∀ i, (F i).card = k

/-- The $r$-wise pair-hitting property: for every $r$ members of the family,
    there exist two elements that together hit all of them. -/
def HasRWisePairHitting {ι : Type*} (F : ι → Finset ℕ) (r : ℕ) : Prop :=
  ∀ (S : Fin r → ι), ∃ x y : ℕ, ∀ j, x ∈ F (S j) ∨ y ∈ F (S j)

/--
**Erdős Problem 644, Part 1** [EFKT92][Er97d]:

Is it true that $f(k,7) = (1+o(1))\frac{3}{4}k$?

For every $\varepsilon > 0$ and all sufficiently large $k$, every family of
$k$-element sets in which every 7 members can be hit by a pair has a
transversal of size at most $(3/4 + \varepsilon)k$, and there exists such a
family requiring a transversal of size at least $(3/4 - \varepsilon)k$.
-/
@[category research open, AMS 5]
theorem erdos_644 :
    answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      (∀ (ι : Type) (F : ι → Finset ℕ),
        IsKUniformFamily F k → HasRWisePairHitting F 7 →
        ∃ T : Finset ℕ, (T.card : ℝ) ≤ (3 / 4 + ε) * (k : ℝ) ∧
          ∀ i : ι, ∃ x ∈ T, x ∈ F i) ∧
      (∃ (ι : Type) (F : ι → Finset ℕ),
        IsKUniformFamily F k ∧ HasRWisePairHitting F 7 ∧
        ∀ T : Finset ℕ, (∀ i : ι, ∃ x ∈ T, x ∈ F i) →
          (T.card : ℝ) ≥ (3 / 4 - ε) * (k : ℝ)) := by
  sorry

/--
**Erdős Problem 644, Part 2** [EFKT92][Er97d]:

For every $r \geq 3$, there exists a constant $c_r > 0$ such that
$f(k,r) = (1+o(1))c_r k$.
-/
@[category research open, AMS 5]
theorem erdos_644.variants.general_constant :
    answer(sorry) ↔
    ∀ r : ℕ, 3 ≤ r →
    ∃ c : ℝ, c > 0 ∧
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      (∀ (ι : Type) (F : ι → Finset ℕ),
        IsKUniformFamily F k → HasRWisePairHitting F r →
        ∃ T : Finset ℕ, (T.card : ℝ) ≤ (c + ε) * (k : ℝ) ∧
          ∀ i : ι, ∃ x ∈ T, x ∈ F i) ∧
      (∃ (ι : Type) (F : ι → Finset ℕ),
        IsKUniformFamily F k ∧ HasRWisePairHitting F r ∧
        ∀ T : Finset ℕ, (∀ i : ι, ∃ x ∈ T, x ∈ F i) →
          (T.card : ℝ) ≥ (c - ε) * (k : ℝ)) := by
  sorry

end Erdos644
