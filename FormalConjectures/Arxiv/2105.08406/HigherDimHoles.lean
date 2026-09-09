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
# Higher-dimensional holes: the Erdős–Szekeres problem in `ℝ³`

This file formalizes questions about `k`-holes of finite point sets in
`d`-dimensional Euclidean space `ℝ^d`, and in particular the case `d = 3`, from
[Sch20].

A `k`-gon is a set of `k` points in *convex position* (convex independent, i.e.
no point lies in the convex hull of the others). A `k`-hole is a `k`-gon whose
convex hull contains no other point of the set. A finite point set is in
*general position* in `ℝ^d` if no `d + 1` of its points lie on a common
hyperplane; we encode this by requiring every `(d + 1)`-subset to be affinely
independent. In the plane this is the empty variant of the Erdős–Szekeres problem
(the Happy Ending problem, `FormalConjectures.ErdosProblems.«107»`), and the
counting question for planar `k`-holes is `FormalConjectures.Arxiv.«2603.18484».EmptyKGons`.

Let `H(d)` be the largest `k` such that every sufficiently large point set in
general position in `ℝ^d` contains a `k`-hole. For the plane `H(2) = 6`: Horton
constructed arbitrarily large sets with no `7`-hole, while the empty-hexagon
theorem guarantees a `6`-hole in every sufficiently large set. For `ℝ³` [Sch20]
proves

* `h^{(3)}(7) ≤ 14`: every set of at least `14` points in general position in
  `ℝ³` contains a `7`-hole (so `H(3) ≥ 7`), and
* there are arbitrarily large sets in general position in `ℝ³` with no
  `23`-hole (so `H(3) ≤ 22`).

Hence `7 ≤ H(3) ≤ 22`. Whether every sufficiently large set in general position
in `ℝ³` contains an `8`-hole, i.e. whether `H(3) ≥ 8`, is **open** (a question of
Valtr).

*References:*
- [Sch] M. Scheucher, *A SAT attack on Erdős–Szekeres numbers in `ℝ^d` and the
  empty hexagon theorem*, Computing in Geometry and Topology 2(1) (2023),
  [doi:10.57717/cgt.v2i1.12](https://doi.org/10.57717/cgt.v2i1.12). Preprint (as
  *A SAT attack on higher dimensional Erdős–Szekeres numbers*), arXiv:2105.08406.
  Establishes `h^{(3)}(7) ≤ 14` and `7 ≤ H(3) ≤ 22`; existence of `8`-holes in
  `ℝ³` (Valtr's question) is open.
-/

open scoped Finset

open EuclideanGeometry

namespace HigherDimHoles

/-- `ℝ^d`, `d`-dimensional Euclidean space; the dimension-generic
`EuclideanGeometry.EDim`. -/
abbrev Space (d : ℕ) := EDim d

/--
**Valtr's question (open).** Do `8`-holes always eventually appear in `ℝ³`?
That is, is there a bound `N` such that every set of at least `N` points in
general position in `ℝ³` contains an `8`-hole (equivalently `H(3) ≥ 8`)?

This is the central open problem of [Sch20]; it is currently unknown. Known:
`7 ≤ H(3) ≤ 22` (see `h3_7_upper_bound` and `no_23_hole_arbitrarily_large`).
-/
@[category research open, AMS 52]
theorem eightHoles_in_space3 :
    answer(sorry) ↔
      ∃ N : ℕ, ∀ P : Finset (Space 3),
        InGenPos P → N ≤ P.card → HasKHole 8 (↑P) := by
  sorry

/--
`h^{(3)}(7) ≤ 14`: every set of at least `14` points in general position in `ℝ³`
contains a `7`-hole [Sch20]. In particular `H(3) ≥ 7`.
-/
@[category research solved, AMS 52]
theorem h3_7_upper_bound :
    ∀ P : Finset (Space 3), InGenPos P → 14 ≤ P.card → HasKHole 7 (↑P) := by
  sorry

/--
There are arbitrarily large point sets in general position in `ℝ³` with no
`23`-hole [Sch20]. In particular `H(3) ≤ 22`.
-/
@[category research solved, AMS 52]
theorem no_23_hole_arbitrarily_large :
    ∀ N : ℕ, ∃ P : Finset (Space 3),
      InGenPos P ∧ N ≤ P.card ∧ ¬ HasKHole 23 (↑P) := by
  sorry

end HigherDimHoles
