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
# Las Vergnas simplex conjecture

A *tope* of an oriented matroid is a maximal covector (a chamber of the associated
pseudohyperplane arrangement). A tope is *simplicial* when it is bounded by exactly
`r` pseudohyperplanes, i.e. it is a simplex. In terms of the chirotope, simplicial
topes are exactly the *mutations*: the flippable `r`-subsets `I` of the ground set,
where reversing the sign of `χ` on `I` again yields a (uniform) chirotope. See
`OrientedMatroid.IsMutation`.

**Las Vergnas' simplex conjecture** asserts that every uniform (simple) oriented
matroid of rank `r ≥ 1` has at least one simplicial tope, equivalently at least one
mutation. It is open in general; the rank-`3` case is a classical theorem of Levi
(and Shannon): every simple arrangement of `n` pseudolines has at least `n`
simplicial cells (triangles), so in particular at least one.

The realizable case (a genuine arrangement of hyperplanes) is also classical, but the
shared chirotope infrastructure carries no `realizable` predicate, so that variant is
omitted here rather than encoded artificially.

*References:*
- A. Björner, M. Las Vergnas, B. Sturmfels, N. White, G. M. Ziegler,
  *Oriented Matroids*, Encyclopedia of Mathematics and its Applications 46,
  Cambridge University Press, 1993/1999 (Exercise 7.29; §2.3 for topes).
- F. Levi, *Die Teilung der projektiven Ebene durch Gerade oder Pseudogerade*,
  Ber. Math.-Phys. Kl. Sächs. Akad. Wiss. **78** (1926), 256–267.
- R. W. Shannon, *Simplicial cells in arrangements of hyperplanes*,
  Geom. Dedicata **8** (1979), 179–187.
-/

open OrientedMatroid

namespace LasVergnasSimplex

/--
**Las Vergnas simplex conjecture.** Every uniform (simple) chirotope of rank `r`
on the ground set `Fin n`, with `1 ≤ r ≤ n`, admits at least one mutation, i.e.
at least one simplicial tope: there is an `r`-subset `I` of the ground set that is
flippable. This is open in general.
-/
@[category research open, AMS 52 5]
theorem las_vergnas_simplex (r n : ℕ) (hr : 1 ≤ r) (hn : r ≤ n)
    (χ : Chirotope r n) (hχ : IsUniformChirotope r n χ) :
    ∃ I : Finset (Fin n), IsMutation χ I := by
  sorry

namespace variants

/--
**Rank-3 case (Levi–Shannon).** Every uniform chirotope of rank `3` on `Fin n`
(with `3 ≤ n`) has a mutation, i.e. every simple arrangement of `n` pseudolines has
a simplicial cell (triangle). This is the classical, solved specialization of the
Las Vergnas simplex conjecture; Levi and Shannon in fact guarantee at least `n` such
triangles.
-/
@[category research solved, AMS 52 5]
theorem rank_three (n : ℕ) (hn : 3 ≤ n)
    (χ : Chirotope 3 n) (hχ : IsUniformChirotope 3 n χ) :
    ∃ I : Finset (Fin n), IsMutation χ I := by
  sorry

/--
**Rank-3 lower bound (Levi–Shannon).** Every simple arrangement of `n ≥ 3`
pseudolines has at least `n` simplicial cells (triangles): the number of mutations of
a uniform rank-`3` chirotope on `Fin n` is at least `n`. This sharper, solved bound
implies `rank_three`.
-/
@[category research solved, AMS 52 5]
theorem rank_three_lower_bound (n : ℕ) (hn : 3 ≤ n)
    (χ : Chirotope 3 n) (hχ : IsUniformChirotope 3 n χ) :
    n ≤ numMutations χ := by
  sorry

end variants

end LasVergnasSimplex
