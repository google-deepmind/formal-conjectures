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
# The Two-Colored (Bichromatic) Triangle Conjecture

A *simple* arrangement of `n` pseudolines in the projective plane is a rank-`3`
uniform oriented matroid, encoded here by a uniform chirotope
`χ : (Fin 3 → Fin n) → SignType`. The pseudolines are the ground-set elements
`Fin n`. A *triangle* (triangular cell) of the arrangement is a simplicial cell
bounded by three of the pseudolines; in the oriented-matroid language these are
exactly the *mutations* of `χ`, the flippable `3`-subsets `I` with `|I| = 3`.

Now `2`-color the pseudolines by `col : Fin n → Bool` (say `false` = red,
`true` = blue). The coloring is *non-trivial* if it uses both colors: at least one
red element and at least one blue element. A triangle `I` (a mutation, `|I| = 3`)
is *bichromatic* if its three bounding lines are not all the same color, i.e. `I`
contains both a red and a blue element.

**Two-Colored Triangle Conjecture.** Every non-trivial `2`-coloring of a simple
pseudoline arrangement has at least one bichromatic triangle. Equivalently, in the
negated (SAT-counterexample) form: no rank-`3` uniform chirotope admits a
non-trivial `2`-coloring in which *every* triangle (mutation) is monochromatic.

We reuse the shared chirotope infrastructure from
`FormalConjecturesForMathlib.Combinatorics.OrientedMatroid.Chirotope`
(`OrientedMatroid.Chirotope`, `IsUniformChirotope`, `IsMutation`, …); it is
reachable through `FormalConjecturesUtil`.

*References:*
- [RKL26] Y. A. Radtke, B. Keszegh, and R. Lauff, *On triangles in colored
  pseudoline arrangements*, [arXiv:2601.20574](https://arxiv.org/abs/2601.20574),
  which states this as the **Two-Colored Triangle Conjecture**.
- [FS21] S. Felsner and M. Scheucher, *Arrangements of pseudocircles: triangles
  and drawings*, Discrete Comput. Geom. 65 (2021), 261–278.
  [doi:10.1007/s00454-020-00173-4](https://doi.org/10.1007/s00454-020-00173-4),
  arXiv:1708.06449.
- [BLSWZ93] A. Björner, M. Las Vergnas, B. Sturmfels, N. White, and G. M. Ziegler,
  *Oriented Matroids*, Encyclopedia of Mathematics and its Applications 46,
  Cambridge University Press, 1993 (the conjecture is stated there, near the
  simplicial-tope material, §4 / p. 280).
-/

open OrientedMatroid

namespace TwoColoredTriangle

variable {n : ℕ}

/-- A triangle `I` (an `r`-subset of the ground set) is **monochromatic** for the
`2`-coloring `col : Fin n → Bool` if all of its incident elements have the same
color: any two of its bounding lines share a color. -/
def IsMonochromatic (col : Fin n → Bool) (I : Finset (Fin n)) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, col x = col y

/-- A triangle `I` (an `r`-subset of the ground set) is **bichromatic** for the
`2`-coloring `col : Fin n → Bool` if it contains both a red element (`col x = false`)
and a blue element (`col y = true`); equivalently, its bounding lines are not all
the same color. For a nonempty `I` this is exactly `¬ IsMonochromatic col I`. -/
def IsBichromatic (col : Fin n → Bool) (I : Finset (Fin n)) : Prop :=
  (∃ x ∈ I, col x = false) ∧ (∃ y ∈ I, col y = true)

/--
**The Two-Colored Triangle Conjecture (arXiv:2601.20574).** Every non-trivial
`2`-coloring of a simple pseudoline arrangement has a bichromatic triangle. Here
the arrangement is a uniform chirotope `χ` of rank `3` on `Fin n`, a triangle is a
mutation (`IsMutation χ I`, an `I` with `|I| = 3`), and the coloring
`col : Fin n → Bool` is non-trivial (`hred`, `hblue` provide a red and a blue
element). The size hypothesis `3 ≤ n` ensures triangles can exist.

Equivalent negated form: no rank-`3` uniform chirotope with a non-trivial
`2`-coloring has all triangles (mutations) monochromatic (`IsMonochromatic`).
-/
@[category research open, AMS 52 5]
theorem two_colored_triangle (n : ℕ) (hn : 3 ≤ n) (χ : Chirotope 3 n)
    (hχ : IsUniformChirotope 3 n χ) (col : Fin n → Bool)
    (hred : ∃ x, col x = false) (hblue : ∃ y, col y = true) :
    ∃ I : Finset (Fin n), IsMutation χ I ∧ IsBichromatic col I := by
  sorry

namespace variants

/--
**The realizable (straight-line) case, known.** For a genuine arrangement of `n`
straight lines in the real projective plane — a *realizable* rank-`3` uniform
oriented matroid — every non-trivial `2`-coloring has a bichromatic triangle. We
model realizability by exhibiting `n` points `p : Fin n → ℝ × ℝ` whose induced
orientation chirotope equals `χ`: for every tuple, `χ t` is the sign of the triple
orientation `orient (p (t 0)) (p (t 1)) (p (t 2))`, the standard `2×2` determinant
`(b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)` measuring the turn
direction of `a → b → c`. The straight-line case has a simple direct argument and
is known to hold.
-/
@[category research solved, AMS 52 5]
theorem two_colored_triangle_realizable (n : ℕ) (hn : 3 ≤ n) (χ : Chirotope 3 n)
    (hχ : IsUniformChirotope 3 n χ)
    (hreal : ∃ p : Fin n → ℝ × ℝ, ∀ t : Fin 3 → Fin n,
      let orient : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ → ℝ :=
        fun a b c => (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)
      χ t = SignType.sign (orient (p (t 0)) (p (t 1)) (p (t 2))))
    (col : Fin n → Bool) (hred : ∃ x, col x = false) (hblue : ∃ y, col y = true) :
    ∃ I : Finset (Fin n), IsMutation χ I ∧ IsBichromatic col I := by
  sorry

end variants

end TwoColoredTriangle
