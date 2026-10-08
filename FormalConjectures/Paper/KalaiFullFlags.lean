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
# Kalai's full flag conjecture

Does every centrally symmetric $n$-dimensional convex polytope, for $n ≥ 1$,
have at least $2^n n!$ complete flags [SZ11, Section 10, p. 21]?
A complete flag is a chain of nonempty proper faces of dimensions
$0, \ldots, n-1$. The answer is affirmative [Ki26].

*References:*
- [SZ11] M. W. Schmitt and G. M. Ziegler, *Ten Problems in Geometry*,
  preprint dated May 1, 2011, Section 10, p. 21,
  https://www.mi.fu-berlin.de/math/groups/discgeom/ziegler/Preprintfiles/127PREPRINT.pdf.
- [Ki26] Kenta Kitamura, *Kalai's full flag conjecture in Lean 4* (2026),
  https://github.com/KitaKen1/funk-volume-kalai-flags.
-/

@[expose] public section

namespace Funk.FormalConjectures

/-- A compact convex body, symmetric about the origin, with nonempty interior. -/
def IsSymmetricConvexBody {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (∀ x ∈ K, -x ∈ K) ∧ 0 ∈ interior K

/-- A polytope is the convex hull of finitely many points. -/
def IsFinitePolytope {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ vertices : Finset (Fin n → ℝ), P = convexHull ℝ (vertices : Set (Fin n → ℝ))

/-- A complete flag consists of one nonempty proper face in each dimension,
ordered by strict inclusion. Nonemptiness excludes the empty face. -/
structure FullFlag {n : ℕ} (P : Set (Fin n → ℝ)) where
  faces : Fin n → Set (Fin n → ℝ)
  nonempty : ∀ i, (faces i).Nonempty
  convex : ∀ i, Convex ℝ (faces i)
  extreme : ∀ i, IsExtreme ℝ P (faces i)
  proper : ∀ i, faces i ⊂ P
  dimension : ∀ i, Module.finrank ℝ (affineSpan ℝ (faces i)).direction = i.val
  chain : StrictMono faces

/-- Kalai's full flag conjecture (2008) [SZ11, Section 10, p. 21]: does every centrally symmetric
$n$-dimensional convex polytope have at least $2^n n!$ complete flags?
The answer is affirmative [Ki26]. -/
@[category research solved, AMS 52,
    formal_proof using lean4 at "https://github.com/KitaKen1/funk-volume-kalai-flags/blob/5b92194f6b5ed49f380a6412b120ad256d850740/lean/FinalTheorems.lean#L90-L106"]
theorem kalaiFullFlags :
    answer(True) ↔
      ∀ (n : ℕ), 1 ≤ n → ∀ (P : Set (Fin n → ℝ)),
        IsFinitePolytope P → IsSymmetricConvexBody P →
          Finite (FullFlag P) ∧
            2 ^ n * n.factorial ≤ Nat.card (FullFlag P) := by
  sorry

end Funk.FormalConjectures
