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
# Erdős Problem 735

*References:*
- [erdosproblems.com/735](https://www.erdosproblems.com/735)
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica 1 (1981), 25-42. [PDF](https://www.renyi.hu/~p_erdos/1981-16.pdf)
- [ABKPR08] Ackerman, E., Buchin, K., Knauer, C., Pinchasi, R. and Rote, G., *There are not too
  many magic configurations*. Discrete Comput. Geom. 39 (2008), 3-16.
  [DOI](https://doi.org/10.1007/s00454-007-9023-0)
-/

@[expose] public section

open EuclideanGeometry

namespace Erdos735

open scoped Classical in
/-- A finite set `S` of points of the plane is *magic* if one can give positive weights to the
points of `S` such that the sum of the weights of the points of `S` on every line containing at
least two points of `S` is the same number `c`. A line containing at least two points of `S` is
`line[ℝ, p, q]` for some distinct `p q ∈ S`. If `S` has at most one point there is no such line,
so `S` is magic. Rescaling the weights, `c` can be normalised to `1` when `S` has two points or
more, which is the definition in [ABKPR08]. -/
def IsMagic (S : Finset ℝ²) : Prop :=
  ∃ (w : ℝ² → ℝ) (c : ℝ), (∀ p ∈ S, 0 < w p) ∧
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∑ r ∈ S with r ∈ line[ℝ, p, q], w r = c

/-- A set with at most one point is magic: there is no line to check. -/
@[category API, AMS 52]
theorem isMagic_of_card_le_one {S : Finset ℝ²} (h : S.card ≤ 1) : IsMagic S :=
  ⟨fun _ => 1, 0, fun _ _ => one_pos,
    fun p hp q hq hpq => absurd (Finset.card_le_one.mp h p hp q hq) hpq⟩

/-- `S` is a *failed Fano configuration*: it consists of four points `a b c d`, no three on a
line, together with the three diagonal points `e = ab ∩ cd`, `f = ac ∩ bd`, `g = ad ∩ bc` of the
complete quadrangle `abcd`. This is the Fano plane with one line removed: the diagonal points are
not collinear in the real plane. The three diagonal points must exist in the plane, that is, the
opposite sides of the quadrangle must not be parallel. Such an `S` has seven points. These are
exactly the projective images of the configuration in Figure 1 of [ABKPR08] that lie in the plane.
Murty's configuration [Er81], "a triangle the angle bisectors and the incentre", is read as the
triangle `abc`, its incentre `d` and the feet `e f g` of the angle bisectors on the opposite
sides. -/
def IsFailedFano (S : Finset ℝ²) : Prop :=
  ∃ a b c d e f g : ℝ²,
    ¬ Collinear ℝ {a, b, c} ∧ ¬ Collinear ℝ {a, b, d} ∧
    ¬ Collinear ℝ {a, c, d} ∧ ¬ Collinear ℝ {b, c, d} ∧
    e ∈ line[ℝ, a, b] ∧ e ∈ line[ℝ, c, d] ∧
    f ∈ line[ℝ, a, c] ∧ f ∈ line[ℝ, b, d] ∧
    g ∈ line[ℝ, a, d] ∧ g ∈ line[ℝ, b, c] ∧
    (S : Set ℝ²) = {a, b, c, d, e, f, g}

/-- The finite sets of points of the plane that can be given positive weights as in the problem:
all points on a line, no three points on a line, all points but one on a line, or a failed Fano
configuration. The cases overlap for small sets. -/
def erdos_735.answer : Set (Finset ℝ²) :=
  {S | Collinear ℝ (S : Set ℝ²) ∨ (∃ p ∈ S, Collinear ℝ ((S : Set ℝ²) \ {p})) ∨
    NonTrilinear (S : Set ℝ²) ∨ IsFailedFano S}

/--
Given any $n$ points in $\mathbb{R}^2$ when can one give positive weights to the points such that
the sum of the weights of the points along every line containing at least two points is the same?

This is a problem of Murty [Er81], who conjectured that this is only possible in one of
four cases: all points on a line, no three points on a line, $n-1$ points on a line, and a
triangle, the angle bisectors, and the incentre (or a projective equivalent). Ackerman, Buchin,
Knauer, Pinchasi and Rote [ABKPR08] proved this conjecture. Conversely, every set in these four
cases is magic.
-/
@[category research solved, question value, AMS 51 52]
theorem erdos_735 : {S : Finset ℝ² | IsMagic S} = erdos_735.answer := by
  sorry

end Erdos735
