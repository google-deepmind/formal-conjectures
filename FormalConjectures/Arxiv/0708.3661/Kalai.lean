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
# Kalai's three-to-the-d conjecture

Kalai's Conjecture A states that every centrally symmetric $d$-dimensional convex polytope
has at least $3^d$ nonempty faces. The count includes the polytope itself and excludes
the empty face. The general conjecture remains open.

Sanyal, Werner and Ziegler [SWZ09, Theorem 1.1] established the bound for $d \leq 4$.
The dimension-five case has an external Lean proof [Ki26]. The unrestricted statement
for $d \geq 6$ remains open. All four statements below concern Conjecture A.

Polytopes are represented as finite convex hulls in Euclidean space. Nonempty interior
expresses full dimension. The centre of symmetry is placed at the origin by translation.
For polytopes, the nonempty exposed faces are exactly the nonempty faces. Dimension zero
is included; its bound is the elementary $3^0 = 1$ case.

*References:*
* [SWZ09] R. Sanyal, A. Werner, G. M. Ziegler, *On Kalai's conjectures concerning centrally
  symmetric polytopes*, Discrete Comput. Geom. 41 (2009), 183–198,
  [arXiv:0708.3661](https://arxiv.org/abs/0708.3661), Conjecture A and Theorem 1.1.
* [Ki26] K. Kitamura, *Kalai's three-to-the-d bound in dimension five*, external Lean proof
  (2026), https://github.com/KitaKen1/kalai-three-pow-five.
-/

@[expose] public section

namespace Kalai

/-- Conjecture A in [SWZ09]: every centrally symmetric $d$-polytope has
at least $3^d$ nonempty faces, including the polytope itself. -/
@[category research open, AMS 52]
theorem three_pow
    (d : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (hpoly : ∃ V : Finset (EuclideanSpace ℝ (Fin d)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin d))))
    (hfull : (interior P).Nonempty)
    (hsymm : ∀ x ∈ P, -x ∈ P) :
    3 ^ d ≤ {F : Set (EuclideanSpace ℝ (Fin d)) |
      F.Nonempty ∧ IsExposed ℝ P F}.ncard := by
  sorry

/-- For $d \leq 4$, every centrally symmetric $d$-polytope has at least $3^d$
nonempty faces [SWZ09, Theorem 1.1]. The zero-dimensional case is immediate. -/
@[category research solved, AMS 52]
theorem three_pow_le_four
    (d : ℕ) (hd : d ≤ 4)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (hpoly : ∃ V : Finset (EuclideanSpace ℝ (Fin d)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin d))))
    (hfull : (interior P).Nonempty)
    (hsymm : ∀ x ∈ P, -x ∈ P) :
    3 ^ d ≤ {F : Set (EuclideanSpace ℝ (Fin d)) |
      F.Nonempty ∧ IsExposed ℝ P F}.ncard := by
  sorry

/-- Every centrally symmetric five-dimensional polytope has at least $3^5 = 243$
nonempty faces. An external Lean proof is given in [Ki26]. -/
@[category research solved, AMS 52,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/kalai-three-pow-five/blob/38bc3bb25949bc33de05bbd169a6012aa0b05165/lean/KalaiFast.lean#L832-L841"]
theorem three_pow_five
    (P : Set (EuclideanSpace ℝ (Fin 5)))
    (hpoly : ∃ V : Finset (EuclideanSpace ℝ (Fin 5)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin 5))))
    (hfull : (interior P).Nonempty)
    (hsymm : ∀ x ∈ P, -x ∈ P) :
    3 ^ 5 ≤ {F : Set (EuclideanSpace ℝ (Fin 5)) |
      F.Nonempty ∧ IsExposed ℝ P F}.ncard := by
  sorry

/-- For $6 \leq d$, every centrally symmetric $d$-polytope is conjectured to have
at least $3^d$ nonempty faces [SWZ09, Conjecture A]. -/
@[category research open, AMS 52]
theorem three_pow_ge_six
    (d : ℕ) (hd : 6 ≤ d)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (hpoly : ∃ V : Finset (EuclideanSpace ℝ (Fin d)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin d))))
    (hfull : (interior P).Nonempty)
    (hsymm : ∀ x ∈ P, -x ∈ P) :
    3 ^ d ≤ {F : Set (EuclideanSpace ℝ (Fin d)) |
      F.Nonempty ∧ IsExposed ℝ P F}.ncard := by
  sorry

end Kalai
