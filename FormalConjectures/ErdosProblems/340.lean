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

open Filter Finset
open scoped Real Pointwise

namespace Erdos340

@[category test, AMS 5]
theorem greedySidon_go_singleton_two : (greedySidon.go {1} (by simp [IsSidon]) 2).val = 2 := by
  decide +native

@[category test, AMS 5]
theorem greedySidon_go_pair_three : (greedySidon.go {1, 2} (by simp [IsSidon]) 3).val = 4 := by
  decide +native

@[category test, AMS 5]
theorem greedySidon_zero : greedySidon 0 = 1 := rfl

@[category test, AMS 5]
theorem greedySidon_one : greedySidon 1 = 2 := by
  decide +native

@[category test, AMS 5]
theorem greedySidon_two : greedySidon 2 = 4 := by
  decide +native

@[category test, AMS 5]
theorem greedySidon_three : greedySidon 3 = 8 := by
  decide +native
@[category test, AMS 5]
theorem greedySidon_four : greedySidon 4 = 13 := by
  decide +native

@[category test, AMS 5]
theorem greedySidon_five : greedySidon 5 = 21 := by
  decide +native

@[category test, AMS 5]
theorem greedySidon_ten : greedySidon 10 = 97 := by
  decide +native

/--
Let $A = \{1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, \ldots\}$ be the greedy Sidon sequence:
we begin with $1$ and iteratively include the next smallest integer that preserves the
Sidon property (i.e. there are no non-trivial solutions to $a + b = c + d$). What is the
order of growth of $A$? Is it true that $|A \cap \{1, \ldots, N\}| \gg N^{1/2 - \varepsilon}$
for all $\varepsilon > 0$ and large $N$?
-/
@[category research open, AMS 5]
theorem erdos_340 (ε : ℝ) (hε : ε > 0) :
    (fun n : ℕ ↦ √n / n ^ ε) =O[atTop]
      fun n : ℕ ↦ ((Set.range greedySidon ∩ Set.Icc 1 n).ncard : ℝ) := by
  sorry

/--
Let $A = \{1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, \ldots\}$ be the greedy Sidon sequence:
we begin with $1$ and iteratively include the next smallest integer that preserves the
Sidon property (i.e. there are no non-trivial solutions to $a + b = c + d$). What is the
order of growth of $A$? Is it true that $|A \cap \{1, \ldots, N\}| \gg N^{1/2 - \varepsilon}$
for all $\varepsilon > 0$ and large $N$?
-/
@[category research open, AMS 5]
theorem erdos_340.variants.isTheta (ε : ℝ) (hε : ε > 0) :
    (fun n : ℕ ↦ ((Set.range greedySidon ∩ Set.Icc 1 n).ncard : ℝ)) =Θ[atTop]
      (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
It is trivial that this sequence grows at least like $\gg N^{1/3}$.
-/
@[category textbook, AMS 5]
theorem erdos_340.variants.third (ε : ℝ) (hε : ε > 0) :
    (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 3)) =O[atTop]
      fun n : ℕ ↦ ((Set.range greedySidon ∩ Set.Icc 1 n).ncard : ℝ) := by
  sorry

/--
Erdős and Graham [ErGr80] also asked about the difference set $A - A$ and whether this has
positive density.

[ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
theory. Monographies de L'Enseignement Mathematique (1980).
-/
@[category research open, AMS 5]
theorem erdos_340.variants.sub_hasPosDensity :
    Set.HasPosDensity (Set.range greedySidon - Set.range greedySidon) := by
  sorry

/--
Erdős and Graham [ErGr80] also asked about the difference set $A - A$ and whether this
contains $22$, which it does.

[ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
theory. Monographies de L'Enseignement Mathematique (1980).
-/
@[category research solved, AMS 5]
theorem erdos_340.variants._22_mem_sub :
    22 ∈ Set.range greedySidon - Set.range greedySidon := by
  sorry

/--
The smallest integer which is unknown to be in $A - A$ is $33$.
 -/
@[category research open, AMS 5]
theorem erdos_340.variants._33_mem_sub : answer(sorry) ↔
    33 ∈ Set.range greedySidon - Set.range greedySidon := by
  sorry

-- Formalisation note: there is some slight ambiguity in the meaning of
-- "almost all" so we provide two variants for "all but finitely many"
-- and "outside of a set of density zero"; there may be other reasonable
-- interpretations
/--
It may be true that all or almost all integers are in $A - A$.
-/
@[category research open, AMS 5]
theorem erdos_340.variants.cofinite_sub : answer(sorry) ↔
    ∀ᶠ n in cofinite, n ∈ Set.range greedySidon - Set.range greedySidon := by
  sorry

/--
It may be true that all or almost all integers are in $A - A$.
-/
@[category research open, AMS 5]
theorem erdos_340.variants.co_density_zero_sub : answer(sorry) ↔
    ∃ S : Set ℕ, S.HasDensity 0 ∧ ∀ n ∈ Sᶜ, n ∈ Set.range greedySidon - Set.range greedySidon := by
  sorry

end Erdos340
