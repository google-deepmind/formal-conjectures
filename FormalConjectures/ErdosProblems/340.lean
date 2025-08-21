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

/-- Given a finite Sidon set `A` and a lower bound `m`, `go` finds the smallest number `m' ≥ m`
such that `A ∪ {m'}` is Sidon. If `A` is empty then this returns the value `m`. Note that
the lower bound is required to avoid `0` being a contender in some cases. -/
private def greedySidon.go (A : Finset ℕ) (hA : IsSidon A.toSet) (m : ℕ) :
    {m' : ℕ // m' ≥ m ∧ m' ∉ A ∧ IsSidon (A ∪ {m'}).toSet} :=
  if h : A.Nonempty then
    ⟨Nat.find (IsSidon.exists_insert_ge h hA m), Nat.find_spec (IsSidon.exists_insert_ge h hA m)⟩
  else ⟨m, by simp_all [IsSidon]⟩

@[category test, AMS 5]
example : (greedySidon.go {1} (by simp [IsSidon]) 2).val = 2 := by
  decide

@[category test, AMS 5]
example : (greedySidon.go {1, 2} (by simp [IsSidon]) 3).val = 4 := by
  decide

/-- Main search loop for generating the greedy Sidon sequence. The return value for step `n` is the
finite set of numbers generated so far, a proof that it is Sidon, and the greatest element of
the finite set at that point. This is initialised at `{1}`, then `greedySidon.go` is
called iteratively using the lower bound `max + 1` to find the next smallest Sidon preserving
number. -/
private def greedySidon.aux (n : ℕ) : ({A : Finset ℕ // IsSidon A.toSet} × ℕ) :=
  match n with
  | 0 => (⟨{1}, by simp [IsSidon]⟩, 1)
  | k + 1 =>
    let (A, s) := greedySidon.aux k
    let s := if h : A.1.Nonempty then A.1.max' h + 1 else s
    let s' := greedySidon.go A.1 A.2 s
    (⟨A ∪ {s'.1}, s'.2.2.2⟩, s')

/-- `greedySidon` is the sequence obtained by the initial set $\{1\}$ and iteratively obtaining
then next smallest integer that preserves the Sidon property of the set. This gives the
sequence `1, 2, 4, 8, 13, 21, 31, ...`. -/
def greedySidon (n : ℕ) : ℕ := greedySidon.aux n |>.2

@[category test, AMS 5]
example : greedySidon 0 = 1 := rfl

@[category test, AMS 5]
example : greedySidon 1 = 2 := by
  decide

@[category test, AMS 5]
example : greedySidon 2 = 4 := by
  decide

@[category test, AMS 5]
example : greedySidon 3 = 8 := by
  decide
@[category test, AMS 5]
example : greedySidon 4 = 13 := by
  decide

@[category test, AMS 5]
example : greedySidon 5 = 21 := by
  decide

@[category test, AMS 5]
example : greedySidon 10 = 97 := by
  decide +native

/--
Let $A = \{1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, \ldots\}$ be the greedy Sidon sequence:
we begin with $1$ and iteratively include the next smallest integer that preserves the
Sidon property (i.e. there are no non-trivial solutions to $a + b = c + d$). What is the
order of growth of $A$? Is it true that $| A \cap\{1, \ldots, N\}| \gg N^{1/2−\varepsilon}$
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
order of growth of $A$? Is it true that $| A \cap\{1, \ldots, N\}| \gg N^{1/2−\varepsilon}$
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
@[category undergraduate, AMS 5]
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

-- Formalisation note: there is some slight ambiguity in the meaning of
-- "almost all" so we provide two variants for "all but finitely many"
-- and "outside of a set of density zero"; there may be other reasonable
-- interpretations
/--
It may be true that all or almost all integers are in $A - A$.
-/
@[category research open, AMS 5]
theorem erdos_340.variants.cofinite_sub :
    (∀ᶠ n in cofinite, n ∈ Set.range greedySidon - Set.range greedySidon) ↔ answer(sorry) :=
  sorry

/--
It may be true that all or almost all integers are in $A - A$.
-/
@[category research open, AMS 5]
theorem erdos_340.variants.co_density_zero_sub :
    (∃ S : Set ℕ, S.HasDensity 0 ∧ ∀ n ∈ Sᶜ, n ∈ Set.range greedySidon - Set.range greedySidon)
      ↔ answer(sorry) :=
  sorry
