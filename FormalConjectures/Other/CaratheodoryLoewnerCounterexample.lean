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
import FormalConjectures.Other.CaratheodoryLoewnerCounterexample.Global

/-!
# The announced smooth counterexamples to the Carathéodory and Loewner conjectures

This module collects the formalization of the explicit counterexample family announced by Levent
Alpöge on 19 August 2026; the announcement credits John-Paul Smith and Claude with checking the
construction. The accompanying file `CaratheodoryLoewnerCounterexample.md` gives the
formalization-oriented informal proof.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/

open scoped ContDiff EuclideanGeometry Manifold

namespace CaratheodoryLoewnerCounterexample

open CaratheodoryConjecture LoewnerConjecture

/-- Alpöge's family disproves every Loewner conjecture whose regularity is no stronger than
smoothness: its member with `k = 1` has an isolated trace-free Hessian zero of winding number
three. -/
@[category research solved, AMS 53 57]
theorem not_loewnerConjectureOfClass_of_le_infty (k : WithTop ℕ∞) (hk : k ≤ ∞) :
    ¬ LoewnerConjectureOfClass k := by
  intro h
  have hbound : (((2 + 1 : ℕ) : ℤ)) ≤ 2 :=
    h (counterexample 1) 0 (((2 + 1 : ℕ) : ℤ))
      ((counterexample_contDiff 1 (by omega)).contDiffAt.of_le hk)
      (counterexample_hasIsolatedZeroIndex 1 (by omega))
  omega

/-- In particular, Alpöge's family disproves the smooth Loewner conjecture. -/
@[category research solved, AMS 53 57]
theorem not_loewnerConjectureOfClass_infty : ¬ LoewnerConjectureOfClass ∞ :=
  not_loewnerConjectureOfClass_of_le_infty ∞ le_rfl

/-- Alpöge's support function disproves every Carathéodory conjecture whose regularity is no
stronger than smoothness: its convex sphere has exactly one umbilic point. -/
@[category research solved, AMS 52 53]
theorem not_caratheodoryConjectureOfClass_of_le_infty (k : WithTop ℕ∞) (hk : k ≤ ∞) :
    ¬ CaratheodoryConjectureOfClass k := by
  intro h
  rcases counterexample_two_is_support_function_with_unique_umbilic with
    ⟨_, F, _, _, _, hsurface, _, _, _, _, _, humbilic, hunique⟩
  rcases hsurface with ⟨hFsmooth, hFembedding, hFinjective, K, hKinterior, hFrange⟩
  have hsurfaceOfClass : IsConvexSphereOfClass k F :=
    ⟨hFsmooth.of_le (add_le_add hk le_rfl), hFembedding, hFinjective,
      K, hKinterior, hFrange⟩
  rcases h F hsurfaceOfClass with
    ⟨p₁, p₂, hpne, hp₁, hp₂⟩
  exact hpne ((hunique p₁ hp₁).trans (hunique p₂ hp₂).symm)

/-- In particular, Alpöge's support function disproves the smooth Carathéodory conjecture. -/
@[category research solved, AMS 52 53]
theorem not_caratheodoryConjectureOfClass_infty : ¬ CaratheodoryConjectureOfClass ∞ :=
  not_caratheodoryConjectureOfClass_of_le_infty ∞ le_rfl

end CaratheodoryLoewnerCounterexample
