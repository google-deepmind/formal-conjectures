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
module

public import FormalConjecturesUtil

/-!
# Residual finiteness of hyperbolic groups

It is an open question whether every hyperbolic group is residually finite. Kapovich and Wise
[KaWi00] proved that this question is equivalent to asking whether every nontrivial hyperbolic
group has a proper subgroup of finite index.

*References:*
- [BMS] G. Baumslag, A. G. Myasnikov and V. Shpilrain, *Open problems in combinatorial group
  theory*, Problem (H1),
  [online](https://shpilrain.ccny.cuny.edu/gworld/problems/probhyp.html).
- [Be04] M. Bestvina, *Questions in geometric group theory*, updated July 2004, Q 1.15,
  [pdf](https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf).
- [KaWi00] I. Kapovich and D. T. Wise, *The equivalence of some residual properties of
  word-hyperbolic groups*, J. Algebra 223 (2000), 562–583,
  [doi:10.1006/jabr.1999.8104](https://doi.org/10.1006/jabr.1999.8104).
-/

@[expose] public section

namespace HyperbolicGroupsResiduallyFinite

/--
Is every hyperbolic group residually finite?

This is Problem (H1)(a) in [BMS] and Q 1.15 in [Be04].
-/
@[category research open, AMS 20]
theorem hyperbolic_residuallyFinite : answer(sorry) ↔
    ∀ (G : Type) [Group G] [Group.IsHyperbolic G], Group.ResiduallyFinite G := by
  sorry

/--
Does every nontrivial hyperbolic group have a proper subgroup of finite index?

This is Problem (H1)(b) in [BMS]. The trivial group has no proper subgroup, so we assume that
$G$ is nontrivial.
-/
@[category research open, AMS 20]
theorem hyperbolic_exists_finiteIndex_ne_top : answer(sorry) ↔
    ∀ (G : Type) [Group G] [Group.IsHyperbolic G] [Nontrivial G],
      ∃ H : Subgroup G, H ≠ ⊤ ∧ H.FiniteIndex := by
  sorry

/--
Every hyperbolic group is residually finite if and only if every nontrivial hyperbolic group has a
proper subgroup of finite index.

This is the theorem of [KaWi00] that Problems (H1)(a) and (H1)(b) are equivalent.
-/
@[category research solved, AMS 20]
theorem hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top :
    (∀ (G : Type) [Group G] [Group.IsHyperbolic G], Group.ResiduallyFinite G) ↔
      ∀ (G : Type) [Group G] [Group.IsHyperbolic G] [Nontrivial G],
        ∃ H : Subgroup G, H ≠ ⊤ ∧ H.FiniteIndex := by
  sorry

end HyperbolicGroupsResiduallyFinite
