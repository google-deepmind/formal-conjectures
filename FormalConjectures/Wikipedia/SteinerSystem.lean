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
# Steiner Systems

A Steiner system $S(t, k, n)$ is a collection of $k$-element subsets (called blocks) of
an $n$-element set such that every $t$-element subset is contained in exactly one block.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Steiner_system)
- [Large Steiner Systems](https://epoch.ai/frontiermath/open-problems/large-steiner-systems)
  by Kunal Marwaha
-/

namespace SteinerSystems

/--
An $S(t, k, n)$-Steiner system is a collection of $k$-element subsets (called blocks) of
$\{0, \ldots, n-1\}$ such that every $t$-element subset is contained in exactly one block.

This is the standard notation from combinatorics, where:
- $n$ is the number of points
- $k$ is the block size
- $t$ is the covering parameter (every $t$-subset is in exactly one block)
-/
structure SteinerSystem (t k n : ℕ) where
  /-- The blocks of the Steiner system. -/
  blocks : Finset (Finset (Fin n))
  /-- Every block has exactly $k$ elements. -/
  block_card : ∀ B ∈ blocks, B.card = k
  /-- Every $t$-element subset is contained in exactly one block.
  Note: We use `.filter.card = 1` instead of `∃!` because `∃! B ∈ blocks, R ⊆ B` desugars to
  a quantifier over all `Finset (Fin n)`, which loses `Decidable` and breaks `native_decide`. -/
  cover_unique : ∀ R : Finset (Fin n), R.card = t → (blocks.filter (R ⊆ ·)).card = 1

/-- Notation for Steiner systems: `S(t, k, n)` denotes a Steiner system with
covering parameter `t`, block size `k`, and `n` points. -/
scoped notation "S(" t ", " k ", " n ")" => SteinerSystem t k n

/--
A constructive witness for a large Steiner system: concrete values of $n$, $k$, $t$
satisfying $n > k > t > 5$, $t < 10$, $n < 200$, together with an explicit Steiner system.
-/
structure LargeSteinerSystemWitness where
  /-- The size of the ground set. -/
  n : ℕ
  /-- The block size. -/
  k : ℕ
  /-- The covering parameter. -/
  t : ℕ
  h_nk : n > k
  h_kt : k > t
  h_t_lower : t > 5
  h_t_upper : t < 10
  h_n_upper : n < 200
  /-- The explicit Steiner system. -/
  system : S(t, k, n)

/--
Construct an $S(t, k, n)$-Steiner system with $n > k > t > 5$, $t < 10$, and $n < 200$.

No example of a Steiner system with $t > 5$ is known, despite a 2014 existence theorem
by Keevash showing that such systems must exist for sufficiently large $n$.

*Reference:* [Large Steiner Systems](https://epoch.ai/frontiermath/open-problems/large-steiner-systems)
-/
@[category research open, AMS 5]
def large_steiner_systems : LargeSteinerSystemWitness := by
  sorry

/--
Sanity check: the Fano plane is an $S(2, 3, 7)$-Steiner system.

The Fano plane consists of $7$ blocks of size $3$ over $7$ points,
where every pair of points is contained in exactly one block.
-/
@[category test, AMS 5]
def fano_plane : S(2, 3, 7) :=
  ⟨{{(0 : Fin 7), 1, 3}, {1, 2, 4}, {2, 3, 5},
    {3, 4, 6}, {0, 4, 5}, {1, 5, 6}, {0, 2, 6}},
   by native_decide, by native_decide⟩

/--
**Existence of $S(5, 6, 12)$**: The small Witt design.

There exists a unique Steiner system $S(5, 6, 12)$, known as the small Witt design.
It was constructed by Witt (1938) and is closely related to the Mathieu group $M_{12}$.
This is one of only two known Steiner systems with $t = 5$.
-/
@[category research solved, AMS 5]
theorem steiner_system_5_6_12 : Nonempty S(5, 6, 12) := by
  sorry

/--
**Existence of $S(5, 8, 24)$**: The large Witt design.

There exists a unique Steiner system $S(5, 8, 24)$, known as the large Witt design.
It was constructed by Witt (1938) and is closely related to the Mathieu group $M_{24}$.
This is one of only two known Steiner systems with $t = 5$.
-/
@[category research solved, AMS 5]
theorem steiner_system_5_8_24 : Nonempty S(5, 8, 24) := by
  sorry

/--
**There are infinitely many Steiner systems with $t = 4$.**

Keevash (2014) proved that for any fixed $t$ and $k$, a Steiner system $S(t, k, n)$
exists for all sufficiently large $n$ satisfying the necessary divisibility conditions.
Since there are infinitely many such admissible $n$, this implies infinitely many
$S(4, k, n)$ systems exist (for any fixed $k > 4$). The proof is nonconstructive.

Explicit examples include $S(4, 5, 11)$ (the unique system, related to the Mathieu
group $M_{11}$) and $S(4, 7, 23)$ (related to the Mathieu group $M_{23}$).
-/
@[category research solved, AMS 5]
theorem infinitely_many_steiner_t4 :
    ∃ S : Set (Σ k n : ℕ, S(4, k, n)), S.Infinite := by
  sorry

/--
**There are infinitely many Steiner systems with $t = 5$.**

Keevash (2014) proved that for any fixed $t$ and $k$, a Steiner system $S(t, k, n)$
exists for all sufficiently large $n$ satisfying the necessary divisibility conditions.
This settles the long-standing open problem of whether infinitely many $S(5, k, n)$
systems exist. The proof is nonconstructive.

Only two explicit examples are known: $S(5, 6, 12)$ and $S(5, 8, 24)$, both Witt
designs related to the Mathieu groups $M_{12}$ and $M_{24}$ respectively.
No Steiner system with $t \geq 6$ has been explicitly constructed, though Keevash's
result guarantees their existence nonconstructively as well.
-/
@[category research solved, AMS 5]
theorem infinitely_many_steiner_t5 :
    ∃ S : Set (Σ k n : ℕ, S(5, k, n)), S.Infinite := by
  sorry

end SteinerSystems
