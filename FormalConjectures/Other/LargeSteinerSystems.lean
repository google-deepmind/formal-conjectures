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

/-!
# Large Steiner Systems

*Reference:* [Large Steiner Systems](https://epoch.ai/frontiermath/open-problems/large-steiner-systems)

Given a set $S$ of size $n$, an $(n, q, r)$-Steiner system is a collection of $q$-element subsets
(called blocks) of $S$ such that every $r$-element subset of $S$ is contained in exactly one block.

No example of a Steiner system with $r > 5$ is known, despite a theorem (Keevash, 2014) that
Steiner systems exist for all sufficiently large $n$ satisfying the necessary divisibility
conditions. The conjecture asks to explicitly construct one with $n > q > r > 5$, $r < 10$,
and $n < 200$.
-/

namespace LargeSteinerSystems

/--
An $(n, q, r)$-Steiner system is a collection of $q$-element subsets (called blocks) of
$\{0, \ldots, n-1\}$ such that every $r$-element subset is contained in exactly one block.
-/
structure SteinerSystem (n q r : ℕ) where
  /-- The blocks of the Steiner system. -/
  blocks : Finset (Finset (Fin n))
  /-- Every block has exactly $q$ elements. -/
  block_card : ∀ B ∈ blocks, B.card = q
  /-- Every $r$-element subset is contained in exactly one block. -/
  cover_unique : ∀ R : Finset (Fin n), R.card = r → (blocks.filter (R ⊆ ·)).card = 1

/--
A constructive witness for a large Steiner system: concrete values of $n$, $q$, $r$
satisfying $n > q > r > 5$, $r < 10$, $n < 200$, together with an explicit Steiner system.
-/
structure LargeSteinerSystemWitness where
  /-- The size of the ground set. -/
  n : ℕ
  /-- The block size. -/
  q : ℕ
  /-- The covering parameter. -/
  r : ℕ
  h_nq : n > q
  h_qr : q > r
  h_r_lower : r > 5
  h_r_upper : r < 10
  h_n_upper : n < 200
  /-- The explicit Steiner system. -/
  system : SteinerSystem n q r

/--
Construct an $(n, q, r)$-Steiner system with $n > q > r > 5$, $r < 10$, and $n < 200$.

No example of a Steiner system with $r > 5$ is known, despite a 2014 existence theorem
by Keevash showing that such systems must exist for sufficiently large $n$.

*Reference:* [Large Steiner Systems](https://epoch.ai/frontiermath/open-problems/large-steiner-systems)
-/
@[category research open, AMS 5]
def large_steiner_systems : LargeSteinerSystemWitness := by
  sorry

/--
Sanity check: the Fano plane is a $(7, 3, 2)$-Steiner system.

The Fano plane consists of $7$ blocks of size $3$ over $7$ points,
where every pair of points is contained in exactly one block.
-/
@[category test, AMS 5]
def fano_plane : SteinerSystem 7 3 2 :=
  ⟨{{(0 : Fin 7), 1, 3}, {1, 2, 4}, {2, 3, 5},
    {3, 4, 6}, {0, 4, 5}, {1, 5, 6}, {0, 2, 6}},
   by native_decide, by native_decide⟩

end LargeSteinerSystems
