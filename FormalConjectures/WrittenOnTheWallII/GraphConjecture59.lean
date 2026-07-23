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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 59

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [Z. Zhang, A Structured Counterexample to WOWII 59](https://github.com/QDKStorm/wowii59-counterexample)
-/

namespace WrittenOnTheWallII.GraphConjecture59

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 59](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$, the size $f(G)$ of a largest induced forest
satisfies $f(G) \ge \lceil \sqrt{\mathrm{residue}(G) \cdot b(G)} \rceil$, where
$\mathrm{residue}(G)$ is the Havel-Hakimi residue (the number of zeros remaining
after applying the Havel-Hakimi algorithm to the degree sequence until termination)
and $b(G)$ is the size of a largest induced bipartite subgraph.

See: Favaron, Mahéo, Saclé (1991) for the residue; DeLaVina's Graffiti.pc for the conjecture.

This conjecture is false. There is a connected counterexample on 123 vertices
with `residue G = 101`, `b G = 122`, and `G.largestInducedForestSize = 111`.
Indeed, `101 * 122 = 12322 = 111 ^ 2 + 1`, so the conjectured lower bound is 112.
-/
@[category research solved, AMS 5]
theorem conjecture59 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_ : G.Connected),
      ⌈Real.sqrt ((residue G : ℝ) * b G)⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  sorry

-- Sanity checks

/-- The `largestInducedForestSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.largestInducedForestSize := Nat.zero_le _

/-- The residue of $K_2$ equals $1$: degree sequence is $[1, 1]$; one Havel-Hakimi
step gives $[0]$, leaving a single zero. -/
@[category test, AMS 5]
example : residue (⊤ : SimpleGraph (Fin 2)) = 1 := by
  unfold residue; decide +native

/-- The invariant values of the counterexample violate the conjectured inequality. -/
@[category test, AMS 5]
example : ¬(⌈Real.sqrt ((101 : ℝ) * 122)⌉ ≤ (111 : ℝ)) := by
  have hceil : ⌈Real.sqrt ((101 : ℝ) * 122)⌉ = (112 : ℤ) := by
    rw [Int.ceil_eq_iff]
    have hsquare : Real.sqrt (12322 : ℝ) ^ 2 = 12322 := by
      rw [Real.sq_sqrt]
      norm_num
    have hsqrt_nonneg : 0 ≤ Real.sqrt (12322 : ℝ) := Real.sqrt_nonneg _
    norm_num
    constructor <;> nlinarith
  rw [hceil]
  norm_num

end WrittenOnTheWallII.GraphConjecture59
