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
# Written on the Wall II - Conjecture 85

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

The conjecture is false for the lexicographic product $C_5[K_4]$. This graph
has minimum even-distance count $9$ and largest induced-tree order $4$. The
conjectured lower bound is therefore $\lceil\sqrt{1 + 2 \cdot 9}\rceil =
\lceil\sqrt{19}\rceil = 5 > 4$.
-/

namespace WrittenOnTheWallII.GraphConjecture85

open Classical SimpleGraph

/--
WOWII [Conjecture 85](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
asked whether every simple connected graph $G$ satisfies
$\operatorname{tree}(G) \geq
\lceil\sqrt{1 + 2\min_v \operatorname{distEven}(v)}\rceil$.
The answer is no, as witnessed by $C_5[K_4]$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/Kuberwastaken/wowii-63-85-counterexample/blob/cba739842ec59adf7426c180009175b31935701d/lean/WOWII85.lean#L171-L183"]
theorem conjecture85 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) (_h : G.Connected),
      let minDistEven := (Finset.univ.image (G.distEven ·)).min' (by simp)
      ⌈Real.sqrt (1 + 2 * (minDistEven : ℝ))⌉ ≤
        (G.largestInducedTreeSize : ℝ) := by
  sorry

/-- The largest induced-tree order is a natural number. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.largestInducedTreeSize := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture85
