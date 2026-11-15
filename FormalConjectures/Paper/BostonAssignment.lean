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
# Pritchard–Wilson conjecture on the worst assigned rank

*References:*
- G. Pritchard and M. C. Wilson,
  [Asymptotic Welfare Performance of Boston Assignment
  Algorithms](https://doi.org/10.1287/stsy.2022.0104),
  *Stochastic Systems* 13 (2023), 247–270, Section 8.2.

Students draw independent uniform complete strict rankings. Schools have unit capacity and one
common priority order. Applications are truthful. Pritchard and Wilson conjecture linear expected
worst assigned rank for naive Boston.
-/

@[expose] public section

open Filter

namespace PritchardWilson

/-- Expected largest assigned rank under naive Boston. -/
noncomputable def expectedWorstRank (n : ℕ) : ℝ :=
  (∑ p : BostonAssignment.Preferences n, (BostonAssignment.worstRank p : ℝ)) /
    Fintype.card (BostonAssignment.Preferences n)

/--
Pritchard and Wilson conjecture that the expected largest assigned rank under naive Boston is
$\Theta(n)$. Since every assigned rank is at most $n$, it remains to establish this linear
lower bound for all sufficiently large markets.
-/
@[category research open, AMS 60 91]
theorem worst_rank_linear :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * n ≤ expectedWorstRank n := by
  sorry

end PritchardWilson
