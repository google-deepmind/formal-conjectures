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
# Written on the Wall II - Conjecture 430a

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

The conjecture is false for the nonuniform clique blow-up of `P₇` with blob
orders `(1,4,12,19,12,4,1)`. Its independent domination number is three, its
center-neighborhood independence number is two, and its Caro--Wei sum is less
than two. The claimed inequality therefore becomes `3 ≤ 2`.
-/

namespace WrittenOnTheWallII.GraphConjecture430a

open SimpleGraph

/-- The center of a finite graph. -/
noncomputable def centerFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => G.eccent v = G.radius

/-- DeLaViña's `N(S)`: the union of open vertex neighborhoods. This may
intersect `S`. -/
def setNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  Finset.univ.filter fun v => ∃ u ∈ S, G.Adj u v

/-- The exact rational Caro--Wei sum. -/
def caroWei {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  ∑ v : V, 1 / ((G.degree v + 1 : ℕ) : ℚ)

/--
WOWII Conjecture 430a asked whether every connected graph `G` of order
greater than three satisfies
`i(G) ≤ α(G[N(C)]) + 2 floor(CW(G)-1)`.
The answer is no, witnessed by a nonuniform `P₇` clique blow-up.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/Kuberwastaken/c5-k4/blob/85fff48cdd7cc1f743802320fdc94db14d1f841e/lean/GraphConjecture430a.lean#L1-L390"]
theorem conjecture430a : answer(False) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 3 < Fintype.card V →
        (G.indepDominationNumber : ℤ) ≤
          ((G.induce
            (setNeighborhood G (centerFinset G) : Set V)).indepNum : ℤ) +
            2 * ⌊caroWei G - 1⌋ := by
  sorry

end WrittenOnTheWallII.GraphConjecture430a
