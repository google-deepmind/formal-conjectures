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
# Robbins Pentagons and Rationality of Diagonals

A cyclic planar pentagon having rational side lengths and rational enclosed area is called a
*Robbins pentagon*. Named after Robbins [Ro94], [Ro95] for his cyclic pentagon area equation, these
pentagons were investigated by Buchholz and MacDougall [BM08], who proved that integer side lengths
force integer area and even perimeter, and that the five internal diagonals are either all rational
or all irrational. Unable to find any irrational-diagonal example, Buchholz and MacDougall
conjectured that every convex Robbins pentagon has rational diagonals.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Robbins_pentagon)
- [Ro94] D. P. Robbins, *Areas of polygons inscribed in a circle*, Discrete Comput. Geom. **12**
  (1994), 223–236.
- [Ro95] D. P. Robbins, *Areas of polygons inscribed in a circle*, Amer. Math. Monthly **102**
  (1995), no. 6, 523–530.
- [BM08] R. H. Buchholz and J. A. MacDougall, *Cyclic polygons with rational sides and area*,
  J. Number Theory **128** (2008), no. 1, 17–48.
-/

@[expose] public section

namespace RobbinsPentagon

open scoped EuclideanGeometry

/-- Enclosed area of a convex pentagon `p : Fin 5 → ℝ²` with cyclically ordered vertices, summed
across the fan triangulation `(p 0, p 1, p 2)`, `(p 0, p 2, p 3)`, and `(p 0, p 3, p 4)`. -/
noncomputable def convexPentagonArea (p : Fin 5 → ℝ²) : ℝ :=
  |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| +
    |EuclideanGeometry.triangle_area (p 0) (p 2) (p 3)| +
    |EuclideanGeometry.triangle_area (p 0) (p 3) (p 4)|

/-- `p : Fin 5 → ℝ²` is a *convex Robbins pentagon* if `p` forms a strictly convex pentagon in
cyclic vertex order (`IsConvexPolygon`, allowing either cyclic orientation while excluding
self-intersecting pentagrams), lies on a Euclidean circle (`Cospherical`), and has rational
consecutive side lengths together with rational enclosed area `convexPentagonArea p`. -/
def IsConvexRobbinsPentagon (p : Fin 5 → ℝ²) : Prop :=
  EuclideanGeometry.IsConvexPolygon p ∧
    EuclideanGeometry.Cospherical (Set.range p) ∧
    (∀ i : Fin 5, ∃ s : ℚ, dist (p i) (p (finRotate 5 i)) = (s : ℝ)) ∧
    (∃ A : ℚ, convexPentagonArea p = (A : ℝ))

/-- When all five vertices coincide at `c : ℝ²`, `convexPentagonArea` vanishes. -/
@[category test, AMS 11 51]
theorem const_pentagon_area_zero (c : ℝ²) :
    convexPentagonArea (fun _ => c) = 0 := by
  unfold convexPentagonArea EuclideanGeometry.triangle_area
  simp

/-- Every consecutive side of a convex Robbins pentagon has positive length. -/
@[category API, AMS 11 51]
theorem side_pos_of_isConvexRobbinsPentagon {p : Fin 5 → ℝ²}
    (hp : IsConvexRobbinsPentagon p) (i : Fin 5) :
    0 < dist (p i) (p (finRotate 5 i)) := by
  rw [dist_pos]
  intro h
  rcases hp.1 with hccw | hcw
  · have hsign := hccw.sign_oangle_finRotate (by decide : 3 ≤ 5) i
    rw [h, EuclideanGeometry.oangle_self_left] at hsign
    simp at hsign
  · have hrot : -finRotate 5 (-finRotate 5 i) = i :=
      (by decide : ∀ j : Fin 5, -finRotate 5 (-finRotate 5 j) = j) i
    have hsign := hcw.sign_oangle_finRotate (by decide : 3 ≤ 5) (-finRotate 5 i)
    change (∡ (p (-(-finRotate 5 i))) (p (-finRotate 5 (-finRotate 5 i)))
      (p (-finRotate 5 (finRotate 5 (-finRotate 5 i))))).sign = 1 at hsign
    rw [neg_neg, hrot, ← h, EuclideanGeometry.oangle_self_left] at hsign
    simp at hsign

/-- A constant vertex tuple is never an `IsConvexRobbinsPentagon`. -/
@[category test, AMS 11 51]
theorem not_isConvexRobbinsPentagon_const (c : ℝ²) :
    ¬ IsConvexRobbinsPentagon (fun _ => c) := by
  intro hp
  have hpos := side_pos_of_isConvexRobbinsPentagon hp 0
  simp at hpos

/-- For the convex house pentagon `(0, 0), (2, 0), (2, 2), (1, 3), (0, 2)` in `ℝ²`,
`convexPentagonArea` equals $5$. -/
@[category test, AMS 11 51]
theorem house_pentagon_area_five :
    convexPentagonArea ![!₂[0, 0], !₂[2, 0], !₂[2, 2], !₂[1, 3], !₂[0, 2]] = 5 := by
  unfold convexPentagonArea
  change |EuclideanGeometry.triangle_area !₂[0, 0] !₂[2, 0] !₂[2, 2]| +
      |EuclideanGeometry.triangle_area !₂[0, 0] !₂[2, 2] !₂[1, 3]| +
      |EuclideanGeometry.triangle_area !₂[0, 0] !₂[1, 3] !₂[0, 2]| = 5
  norm_num [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- The cyclic pentagon `(25, 0), (7, -24), (-7, -24), (-25, 0), (7, 24)` on $x^2 + y^2 = 25^2$
has enclosed area $1368$. -/
@[category test, AMS 11 51]
theorem robbins_pentagon_example_area :
    convexPentagonArea
      ![!₂[25, 0], !₂[7, -24], !₂[-7, -24], !₂[-25, 0], !₂[7, 24]] = 1368 := by
  unfold convexPentagonArea
  change |EuclideanGeometry.triangle_area !₂[25, 0] !₂[7, -24] !₂[-7, -24]| +
      |EuclideanGeometry.triangle_area !₂[25, 0] !₂[-7, -24] !₂[-25, 0]| +
      |EuclideanGeometry.triangle_area !₂[25, 0] !₂[-25, 0] !₂[7, 24]| = 1368
  norm_num [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- The cyclic pentagon `(25, 0), (7, -24), (-7, -24), (-25, 0), (7, 24)` on $x^2 + y^2 = 25^2$
(consecutive sides $30, 14, 30, 40, 30$ and area $1368$) satisfies `IsConvexRobbinsPentagon`. -/
@[category test, AMS 11 51]
theorem isConvexRobbinsPentagon_example :
    IsConvexRobbinsPentagon
      ![!₂[25, 0], !₂[7, -24], !₂[-7, -24], !₂[-25, 0], !₂[7, 24]] := by
  let p : Fin 5 → ℝ² := ![!₂[25, 0], !₂[7, -24], !₂[-7, -24], !₂[-25, 0], !₂[7, 24]]
  have hdist : ∀ (x y : ℝ²) {r : ℝ}, 0 ≤ r →
      (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = r ^ 2 → dist x y = r := by
    intro x y r hr hsq
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
    simp only [Real.dist_eq, sq_abs]
    rw [hsq, Real.sqrt_sq hr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · let e₀ : ℝ² := !₂[1, 0]
    let e₁ : ℝ² := !₂[0, 1]
    have hvsub : ∀ x y : ℝ², x -ᵥ y = (x 0 - y 0) • e₀ + (x 1 - y 1) • e₁ := by
      intro x y
      ext idx
      fin_cases idx <;> simp [e₀, e₁]
    have hoangle_sign : ∀ a b c : ℝ²,
        (∡ a b c).sign =
          SignType.sign ((a 0 - b 0) * (c 1 - b 1) - (a 1 - b 1) * (c 0 - b 0)) *
            (EuclideanGeometry.o.oangle e₀ e₁).sign := by
      intro a b c
      rw [EuclideanGeometry.oangle, hvsub a b, hvsub c b]
      exact EuclideanGeometry.o.oangle_sign_smul_add_smul_smul_add_smul e₀ e₁ _ _ _ _
    have hli : LinearIndependent ℝ ![e₀, e₁] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg idx
      have h0 := congr_arg (fun v : ℝ² => v 0) hg
      have h1 := congr_arg (fun v : ℝ² => v 1) hg
      simp [Fin.sum_univ_two, e₀, e₁] at h0 h1
      fin_cases idx <;> assumption
    have hs_ne : (EuclideanGeometry.o.oangle e₀ e₁).sign ≠ 0 := by
      rw [ne_eq, Real.Angle.sign_eq_zero_iff,
        EuclideanGeometry.o.oangle_eq_zero_or_eq_pi_iff_not_linearIndependent, not_not]
      exact hli
    cases hs : (EuclideanGeometry.o.oangle e₀ e₁).sign
    · exact (hs_ne hs).elim
    · right
      let q : Fin 5 → ℝ² :=
        ![!₂[25, 0], !₂[7, 24], !₂[-25, 0], !₂[-7, -24], !₂[7, -24]]
      have hneg : (fun i : Fin 5 => p (-i)) = q := by
        ext i idx
        fin_cases i <;> fin_cases idx <;> rfl
      rw [hneg]
      intro i j k hij hjk
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        first
        | (exfalso; revert hij hjk; decide)
        | (dsimp only; rw [hoangle_sign, hs, sign_neg (by norm_num [q])]; rfl)
    · left
      intro i j k hij hjk
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        first
        | (exfalso; revert hij hjk; decide)
        | (dsimp only; rw [hoangle_sign, hs, sign_pos (by norm_num [p])]; rfl)
  · refine ⟨!₂[0, 0], 25, ?_⟩
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> exact hdist _ _ (by norm_num) (by norm_num [p])
  · let r : Fin 5 → ℝ² :=
      ![!₂[7, -24], !₂[-7, -24], !₂[-25, 0], !₂[7, 24], !₂[25, 0]]
    have hrotp : ∀ j : Fin 5, p (finRotate 5 j) = r j := by
      intro j
      ext idx
      fin_cases j <;> fin_cases idx <;> rfl
    intro i
    change ∃ s : ℚ, dist (p i) (p (finRotate 5 i)) = (s : ℝ)
    rw [hrotp i]
    fin_cases i
    · exact ⟨30, hdist _ _ (by norm_num) (by norm_num [p, r])⟩
    · exact ⟨14, hdist _ _ (by norm_num) (by norm_num [p, r])⟩
    · exact ⟨30, hdist _ _ (by norm_num) (by norm_num [p, r])⟩
    · exact ⟨40, hdist _ _ (by norm_num) (by norm_num [p, r])⟩
    · exact ⟨30, hdist _ _ (by norm_num) (by norm_num [p, r])⟩
  · exact ⟨1368, by rw [robbins_pentagon_example_area]; norm_num⟩

/--
Buchholz–MacDougall integrality theorem [BM08]: if a convex Robbins pentagon has integer side
lengths $s_0, \dots, s_4$, then its enclosed area is an integer.
-/
@[category research solved, AMS 11 51]
theorem buchholz_macdougall_integer_area (p : Fin 5 → ℝ²) (s : Fin 5 → ℕ)
    (hp : IsConvexRobbinsPentagon p)
    (hs : ∀ i : Fin 5, dist (p i) (p (finRotate 5 i)) = (s i : ℝ)) :
    ∃ A : ℕ, convexPentagonArea p = (A : ℝ) := by
  sorry

/--
Buchholz–MacDougall parity theorem [BM08]: if a convex Robbins pentagon has integer side lengths
$s_0, \dots, s_4$, then its perimeter $\sum_{i=0}^4 s_i$ is even.
-/
@[category research solved, AMS 11 51]
theorem buchholz_macdougall_even_perimeter (p : Fin 5 → ℝ²) (s : Fin 5 → ℕ)
    (hp : IsConvexRobbinsPentagon p)
    (hs : ∀ i : Fin 5, dist (p i) (p (finRotate 5 i)) = (s i : ℝ)) :
    Even (∑ i : Fin 5, s i) := by
  sorry

/--
Buchholz–MacDougall diagonal dichotomy [BM08]: for any convex Robbins pentagon, its five internal
diagonals are either all rational in length or all irrational in length.
-/
@[category research solved, AMS 11 51]
theorem buchholz_macdougall_robbins_pentagon_dichotomy (p : Fin 5 → ℝ²)
    (hp : IsConvexRobbinsPentagon p) :
    (∀ i j : Fin 5, ∃ q : ℚ, dist (p i) (p j) = (q : ℝ)) ∨
      (∀ i j : Fin 5, i ≠ j → j ≠ finRotate 5 i → i ≠ finRotate 5 j →
        Irrational (dist (p i) (p j))) := by
  sorry

/--
Buchholz–MacDougall rational diagonals conjecture [BM08]: every convex Robbins pentagon has
rational length for all five internal diagonals (equivalently, every pairwise vertex distance is
rational).
-/
@[category research open, AMS 11 51]
theorem robbins_pentagon_rational_diagonals (p : Fin 5 → ℝ²)
    (hp : IsConvexRobbinsPentagon p) (i j : Fin 5) :
    ∃ q : ℚ, dist (p i) (p j) = (q : ℝ) := by
  sorry

end RobbinsPentagon
