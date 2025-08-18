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
open scoped Real Pointwise

local instance (A : Finset ℕ) : Decidable (IsSidon A.toSet) :=
  decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A), _) <| by rfl

private def greedySidon.go (A : Finset ℕ) (m : ℕ) : ℕ :=
  if h : A.Nonempty then
    if m > 2 * A.max' h then 2 * A.max' h + 1
      else if m ∉ A ∧ IsSidon (A ∪ {m}).toSet then m
        else greedySidon.go A (m + 1)
  else 0
termination_by if h : A.Nonempty then (2 * A.max' h + 1 - m) else 0
decreasing_by
  split_ifs
  simp_all [Nat.sub_add_eq]
  linarith

@[category test, AMS 5]
example : greedySidon.go {1} 2 = 2 := by
  decide +kernel

@[category test, AMS 5]
example : greedySidon.go {1, 2} 3 = 4 := by
  decide +kernel

private def greedySidon.aux (n : ℕ) : (Finset ℕ × ℕ) :=
  match n with
  | 0 => ({1}, 2)
  | k + 1 =>
    let (A, s) := greedySidon.aux k
    let s' := greedySidon.go (A ∪ {s}) (s + 1)
    (A ∪ {s}, s')
termination_by n

/-- `greedySidon` is the sequence obtained by the initial set $\{1\}$ and iteratively obtaining
then next smallest integer that preserves the Sidon property of the set. This gives the
sequence `1, 2, 4, 8, 13, 21, 31, ...`. -/
def greedySidon (n : ℕ) : ℕ := match n with
  | 0 => 1
  | m + 1 => greedySidon.aux m |>.2

@[category test, AMS 5]
example : greedySidon 0 = 1 := rfl

@[category test, AMS 5]
example : greedySidon 1 = 2 := by
  simp [greedySidon, greedySidon.aux]

@[category test, AMS 5]
example : greedySidon 2 = 4 := by
  decide +kernel

@[category test, AMS 5]
example : greedySidon 3 = 8 := by
  decide +kernel

@[category test, AMS 5]
example : greedySidon 4 = 13 := by
  decide +kernel

@[category test, AMS 5]
example : greedySidon 5 = 21 := by
  decide +kernel

/--
Let $A = \{1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, \ldots\}$ be the greedy Sidon sequence:
we begin with $1$ and iteratively include the next smallest integer that preserves the
Sidon property (i.e. there are no non-trivial solutions to $a + b = c + d$). What is the
order of growth of $A$? Is it true that $| A \cap\{1, \ldots, N\}| \gg N^{1/2−\varepsilon}$
for all $\varepsilon > 0$ and large $N$?
-/
@[category research open, AMS 5]
theorem erdos_340 (ε : ℝ) (hε : ε > 0) :
    (fun n : ℕ ↦ √n / n ^ ε) =o[atTop]
      fun n : ℕ ↦ ((Set.range greedySidon ∩ Set.Iio n).ncard : ℝ) := by
  sorry

/--
It is trivial that this sequence grows at least like $\gg N^{1/3}$.
-/
@[category undergraduate, AMS 5]
theorem erdos_340.variants.third (ε : ℝ) (hε : ε > 0) :
    (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 3)) =o[atTop]
      fun n : ℕ ↦ ((Set.range greedySidon ∩ Set.Iio n).ncard : ℝ) := by
  sorry

/--
Erdős and Graham [ErGr80] also asked about the difference set $A - A$ and whether this has
positive density.

[ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
theory. Monographies de L'Enseignement Mathematique (1980).
-/
@[category research open, AMS 5]
theorem erdos_340.variants.sub_hasPosDensity :
    Set.HasPosDensity (Set.range greedySidon - Set.range greedySidon) :=
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
theorem erdos_340.variants._33_mem_sub :
    33 ∈ Set.range greedySidon - Set.range greedySidon ↔ answer(sorry) :=
  sorry

/--
It may be true that all or almost all integers are in $A - A$.
-/
@[category research open, AMS 5]
theorem erdos_340.variants.cofinite_sub :
    (∀ᶠ n in cofinite, n ∈ Set.range greedySidon - Set.range greedySidon) ↔ answer(sorry) :=
  sorry
