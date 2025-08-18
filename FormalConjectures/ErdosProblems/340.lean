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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 340

*Reference:* [erdosproblems.com/340](https://www.erdosproblems.com/340)
-/

open Filter
open scoped Real Classical Pointwise

/--
A function `a : ℕ → ℕ` represents the greedy Sidon sequence if it starts with `1`
and iteratively includes the next smallest integer that preserves the Sidon property.
-/
def IsSidon.IsGreedy {a : ℕ → ℕ} (ha : IsSidon (Set.range a)) : Prop :=
  a 0 = 1 ∧ ∀ n, a (n + 1) =
    Nat.find (ha.subset (Finset.coe_image_subset_range (s := Finset.range (n + 1)))).exists_insert

/--
Let $A = \{1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, \ldots\}$ be the greedy Sidon sequence:
we begin with $1$ and iteratively include the next smallest integer that preserves the
Sidon property (i.e. there are no non-trivial solutions to $a + b = c + d$). What is the
order of growth of $A$? Is it true that $| A \cap\{1, \ldots, N\}| \gg N^{1/2−\varepsilon}$
for all $\varepsilon > 0$ and large $N$?
-/
@[category research open, AMS 5]
theorem erdos_340 (ε : ℝ) (hε : ε > 0) (a : ℕ → ℕ) (ha₁ : IsSidon (Set.range a))
    (ha₂ : ha₁.IsGreedy) :
    (fun n : ℕ ↦ √n / n ^ ε) =o[atTop] fun n : ℕ ↦ ((Set.range a ∩ Set.Iio n).ncard : ℝ) := by
  sorry

/--
It is trivial that this sequence grows at least like $\gg N^{1/3}$.
-/
@[category undergraduate, AMS 5]
theorem erdos_340.variants.third (ε : ℝ) (hε : ε > 0) (a : ℕ → ℕ) (ha₁ : IsSidon (Set.range a))
    (ha₂ : ha₁.IsGreedy) :
    (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 3)) =o[atTop]
      fun n : ℕ ↦ ((Set.range a ∩ Set.Iio n).ncard : ℝ) := by
  sorry

/--
Erdős and Graham [ErGr80] also asked about the difference set $A - A$ and whether this has
positive density.

[ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
theory. Monographies de L'Enseignement Mathematique (1980).
-/
@[category research open, AMS 5]
theorem erdos_340.variants.sub_hasPosDensity (a : ℕ → ℕ) (ha₁ : IsSidon (Set.range a))
    (ha₂ : ha₁.IsGreedy) :
    Set.HasPosDensity (Set.range a - Set.range a) :=
  sorry

/--
Erdős and Graham [ErGr80] also asked about the difference set $A - A$ and whether this
contains $22$, which it does.

[ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
theory. Monographies de L'Enseignement Mathematique (1980).
-/
@[category research solved, AMS 5]
theorem erdos_340.variants._22_mem_sub (a : ℕ → ℕ) (ha₁ : IsSidon (Set.range a))
    (ha₂ : ha₁.IsGreedy) :
    22 ∈ Set.range a - Set.range a :=
  sorry

/--
The smallest integer which is unknown to be in $A - A$ is $33$.
 -/
@[category research open, AMS 5]
theorem erdos_340.variants._33_mem_sub (a : ℕ → ℕ) (ha₁ : IsSidon (Set.range a))
    (ha₂ : ha₁.IsGreedy) :
    33 ∈ Set.range a - Set.range a ↔ answer(sorry) :=
  sorry

/--
It may be true that all or almost all integers are in $A - A$.
-/
@[category research open, AMS 5]
theorem erdos_340.variants.cofinite_sub (a : ℕ → ℕ) (ha₁ : IsSidon (Set.range a))
    (ha₂ : ha₁.IsGreedy) :
    (∀ᶠ n in cofinite, n ∈ Set.range a - Set.range a) ↔ answer(sorry) :=
  sorry
