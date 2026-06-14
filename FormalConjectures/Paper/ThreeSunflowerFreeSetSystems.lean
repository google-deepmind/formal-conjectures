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
import FormalConjecturesForMathlib.Combinatorics.SetFamily.Sunflower

/-!
# Three-sunflower-free set systems with bounded pairwise intersections

*References:*
* [Three-sunflower-free set systems with bounded pairwise intersections]
  (https://doi.org/10.5281/zenodo.20693260), by *Cody Mitchell* (2026).
* [sunflower-lean: paper-v2](https://doi.org/10.5281/zenodo.20693191),
  companion Lean 4 formalization, release `paper-v2`.

For `ℓ > t ≥ 1`, the paper studies the maximum size `M₃(ℓ,t)` of a
family of distinct `ℓ`-sets with pairwise intersections of size at most `t`
and no three-sunflower. The empty-core case is included, so three pairwise
disjoint sets form a three-sunflower. The variant `I₃(ℓ,t)` imposes the
additional condition that the family is intersecting.
-/

open Filter

namespace ThreeSunflowerFreeSetSystems

variable {α : Type}

/-- A family is `ℓ`-uniform if every member is finite of cardinality `ℓ`. -/
def IsUniform (ℓ : ℕ) (F : Set (Set α)) : Prop :=
  ∀ A ∈ F, A.Finite ∧ A.ncard = ℓ

/-- Every two distinct members of `F` have intersection size at most `t`. -/
def HasPairwiseIntersectionsAtMost (t : ℕ) (F : Set (Set α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).ncard ≤ t

/-- The family `F` contains no three-member sunflower. -/
def ThreeSunflowerFree (F : Set (Set α)) : Prop :=
  ¬ ∃ S : Set (Set α), S ⊆ F ∧ S.ncard = 3 ∧ IsSunflower S

/--
An admissible family for `M₃(ℓ,t)`: a distinct family of `ℓ`-sets, all
pairwise intersections have size at most `t`, and no three members form a
sunflower.
-/
def M3Admissible (ℓ t : ℕ) (F : Set (Set α)) : Prop :=
  IsUniform ℓ F ∧ HasPairwiseIntersectionsAtMost t F ∧ ThreeSunflowerFree F

/--
An admissible family for `I₃(ℓ,t)`: an admissible family for `M₃(ℓ,t)` with
no disjoint pair.
-/
def I3Admissible (ℓ t : ℕ) (F : Set (Set α)) : Prop :=
  M3Admissible ℓ t F ∧ ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).Nonempty

/--
The extremal number `M₃(ℓ,t)`: the largest size, over finite ground sets, of
a three-sunflower-free `ℓ`-uniform family whose pairwise intersections have
size at most `t`.
-/
noncomputable def M3 (ℓ t : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (α : Type) (_ : Fintype α) (F : Set (Set α)),
    M3Admissible ℓ t F ∧ F.ncard = m}

/--
The intersecting extremal number `I₃(ℓ,t)`: the same maximum as `M₃(ℓ,t)`,
with the additional restriction that the family has no disjoint pair.
-/
noncomputable def I3 (ℓ t : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (α : Type) (_ : Fintype α) (F : Set (Set α)),
    I3Admissible ℓ t F ∧ F.ncard = m}

/--
The restricted-intersection three-sunflower threshold: the least `N` such
that every `n`-uniform family with pairwise intersections of size at most `t`
and at least `N` members contains a three-sunflower.
-/
noncomputable def restrictedThreshold (n t : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ {α : Type}, ∀ F : Set (Set α),
    IsUniform n F → HasPairwiseIntersectionsAtMost t F → N ≤ F.ncard →
      ∃ S ⊆ F, S.ncard = 3 ∧ IsSunflower S}

/-- A natural number is a prime power. -/
def IsPrimePower (q : ℕ) : Prop :=
  ∃ p a : ℕ, p.Prime ∧ 0 < a ∧ q = p ^ a

/--
The two-copy decomposition supplied by the `t = 1` classification: the family
splits into two disjoint intersecting extremal pieces, and every cross pair is
disjoint.
-/
def HasTwoDisjointT1ExtremalPieces (ℓ : ℕ) (F : Set (Set α)) : Prop :=
  ∃ G H : Set (Set α), G ⊆ F ∧ H ⊆ F ∧ F = G ∪ H ∧ Disjoint G H ∧
    I3Admissible ℓ 1 G ∧ I3Admissible ℓ 1 H ∧ G.ncard = ℓ + 1 ∧ H.ncard = ℓ + 1 ∧
    ∀ A ∈ G, ∀ B ∈ H, Disjoint A B

/--
The exact `t = 1` values from Mitchell's paper: for every `ℓ ≥ 2`,
`I₃(ℓ,1) = ℓ + 1` and `M₃(ℓ,1) = 2ℓ + 2`.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/SproutSeeds/sunflower-lean/tree/paper-v2"]
theorem m3_t1_exact (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    I3 ℓ 1 = ℓ + 1 ∧ M3 ℓ 1 = 2 * ℓ + 2 := by
  sorry

/--
The `t = 1` extremal classification implies that every extremal `M₃(ℓ,1)`
family splits into two disjoint intersecting extremal pieces. The companion
Lean development proves the sharper vertex-star incidence classification of
those pieces.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/SproutSeeds/sunflower-lean/tree/paper-v2"]
theorem m3_t1_extremal_decomposition (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : Set (Set α))
    (hF : M3Admissible ℓ 1 F) (hcard : F.ncard = M3 ℓ 1) :
    HasTwoDisjointT1ExtremalPieces ℓ F := by
  sorry

/--
The sharp counting upper bound at `t = 2`: for every `ℓ ≥ 3`,
`M₃(ℓ,2) ≤ 3ℓ² - ℓ + 2`.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/SproutSeeds/sunflower-lean/tree/paper-v2"]
theorem m3_t2_upper_bound (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    M3 ℓ 2 ≤ 3 * ℓ ^ 2 - ℓ + 2 := by
  sorry

/--
The orthogonal-projective-plane construction gives the lower bound
`M₃(2q+2,2) ≥ 2(q²+q+1)` for every prime power `q`.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/SproutSeeds/sunflower-lean/tree/paper-v2"]
theorem m3_t2_prime_power_lower_bound (q : ℕ) (hq : IsPrimePower q) :
    2 * (q ^ 2 + q + 1) ≤ M3 (2 * q + 2) 2 := by
  sorry

/--
The paper's unconditional quadratic lower bound at `t = 2`, obtained from
the prime-power construction by padding and Bertrand's postulate.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/SproutSeeds/sunflower-lean/tree/paper-v2"]
theorem m3_t2_quadratic_lower_bound (ℓ : ℕ) (hℓ : 4 ≤ ℓ) :
    (ℓ - 2) ^ 2 / 8 ≤ M3 ℓ 2 := by
  sorry

/--
Corollary 1.3 of the paper: for bounded pairwise intersections, the
three-sunflower threshold is one more than the extremal number.
-/
@[category research solved, AMS 5]
theorem restricted_threshold_eq_m3_add_one (n t : ℕ) (htn : t < n) :
    restrictedThreshold n t = M3 n t + 1 := by
  sorry

/--
The disjointness graph of a family is Mantel-tight when its ordered disjoint
pairs attain the balanced triangle-free extremal count.
-/
def HasMantelTightDisjointness (F : Set (Set α)) : Prop :=
  {p : Set α × Set α | p.1 ∈ F ∧ p.2 ∈ F ∧ p.1 ≠ p.2 ∧ Disjoint p.1 p.2}.ncard =
    2 * (F.ncard ^ 2 / 4)

/--
The family `F` splits into two intersecting admissible pieces, with every
cross pair disjoint.
-/
def SplitsIntoTwoIntersectingPieces (ℓ t : ℕ) (F : Set (Set α)) : Prop :=
  ∃ G H : Set (Set α), G ⊆ F ∧ H ⊆ F ∧ F = G ∪ H ∧ Disjoint G H ∧
    I3Admissible ℓ t G ∧ I3Admissible ℓ t H ∧
    ∀ A ∈ G, ∀ B ∈ H, Disjoint A B

/--
Version 2 structural reduction at `t = 2`: in the Mantel-tight
disjointness regime, an admissible family is exactly two intersecting
admissible pieces on disjoint supports.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/SproutSeeds/sunflower-lean/tree/paper-v2"]
theorem m3_t2_mantel_tight_reduction {α : Type} (ℓ : ℕ) (F : Set (Set α))
    (hF : M3Admissible ℓ 2 F) (hTight : HasMantelTightDisjointness F) :
    SplitsIntoTwoIntersectingPieces ℓ 2 F := by
  sorry

/--
Open exponent problem from the paper: is `M₃(ℓ,t)` quadratically bounded in
`ℓ` for every fixed `t ≥ 2`?
-/
@[category research open, AMS 5]
theorem m3_fixed_t_quadratic_exponent_problem :
    answer(sorry) ↔
      ∀ t : ℕ, 2 ≤ t → ∃ C : ℕ, ∀ ℓ : ℕ, t < ℓ → M3 ℓ t ≤ C * ℓ ^ 2 := by
  sorry

/--
Open constant problem at `t = 2`: does the normalized sequence
`M₃(ℓ,2) / ℓ²` converge?
-/
@[category research open, AMS 5]
theorem m3_t2_constant_problem :
    answer(sorry) ↔
      ∃ c : ℝ, Tendsto (fun ℓ : ℕ => (M3 ℓ 2 : ℝ) / (ℓ : ℝ) ^ 2) atTop (nhds c) := by
  sorry

/--
Open structural problem at `t = 2`: is two-copy doubling of an optimal
intersecting family asymptotically optimal up to an additive constant?
-/
@[category research open, AMS 5]
theorem m3_t2_doubling_optimal_problem :
    answer(sorry) ↔ ∃ C : ℕ, ∀ ℓ : ℕ, 3 ≤ ℓ → M3 ℓ 2 ≤ 2 * I3 ℓ 2 + C := by
  sorry

end ThreeSunflowerFreeSetSystems
