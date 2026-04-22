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
# Roman Domination Number

*Reference:*
[E. J. Cockayne, P. A. Dreyer, S. M. Hedetniemi, S. T. Hedetniemi,
Roman domination in graphs, Discrete Mathematics 278 (2004) 11–22](https://doi.org/10.1016/j.disc.2003.06.004)

## Definition

A **Roman dominating function** on a graph `G` is a labeling `f : V → {0, 1, 2}`
such that every vertex `v` with `f(v) = 0` has at least one neighbor `w` with
`f(w) = 2`.  The **weight** of `f` is `∑ v, f(v)`.

The **Roman domination number** `γ_R(G)` is the minimum weight over all Roman
dominating functions.

## Conjectures

Two classical results (both resolved) bound `γ_R(G)` in terms of the ordinary
domination number `γ(G)`:

1. `γ(G) ≤ γ_R(G)` — any Roman dominating function of weight `w` yields a
   dominating set of size `≤ w` by taking the support `{v | f(v) ≥ 1}`.

2. `γ_R(G) ≤ 2 · γ(G)` — given a minimum dominating set `D`, define `f(v) = 2`
   for `v ∈ D` and `f(v) = 0` otherwise; this is Roman dominating with weight
   `2 · |D| = 2 · γ(G)`.
-/

namespace WrittenOnTheWallII.GraphRomanDomination

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A **Roman dominating function** is a labeling `f : V → Fin 3` (values 0, 1, 2)
such that every vertex `v` with `f(v) = 0` has a neighbor `w` with `f(w) = 2`. -/
def IsRomanDominatingFunction (G : SimpleGraph α) (f : α → Fin 3) : Prop :=
  ∀ v, (f v).val = 0 → ∃ w, G.Adj v w ∧ (f w).val = 2

/-- The **Roman domination number** `γ_R(G)`: the minimum weight of a Roman
dominating function, where weight = `∑ v, (f v).val`. -/
noncomputable def romanDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {w | ∃ f : α → Fin 3, IsRomanDominatingFunction G f ∧ w = ∑ v, (f v).val}

/-- **Lower bound** (resolved): the Roman domination number is at least the
ordinary domination number, `γ(G) ≤ γ_R(G)`.

Proof sketch: given a Roman dominating function `f` of weight `w`, the set
`{v | f(v) ≥ 1}` is a dominating set of size `≤ w`; hence `γ(G) ≤ w`. -/
@[category research solved, AMS 5]
theorem dominationNumber_le_romanDominationNumber
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    G.dominationNumber ≤ romanDominationNumber G := by
  sorry

/-- **Upper bound** (resolved): `γ_R(G) ≤ 2 · γ(G)`.

Proof sketch: take a minimum dominating set `D`; set `f(v) = 2` for `v ∈ D` and
`f(v) = 0` otherwise.  Every vertex outside `D` has a neighbor in `D` (with
label 2), so `f` is Roman dominating with weight `2 · |D| = 2 · γ(G)`. -/
@[category research solved, AMS 5]
theorem romanDominationNumber_le_two_mul_dominationNumber
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    romanDominationNumber G ≤ 2 * G.dominationNumber := by
  sorry

-- Sanity checks

/-- `romanDominationNumber` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ romanDominationNumber G :=
  Nat.zero_le _

/-- `IsRomanDominatingFunction` is a well-formed proposition on small graphs. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (f : Fin 3 → Fin 3) :
    IsRomanDominatingFunction G f ∨ True :=
  Or.inr trivial

/-- `romanDominationNumber` cast to `ℝ` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : (0 : ℝ) ≤ (romanDominationNumber G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphRomanDomination
