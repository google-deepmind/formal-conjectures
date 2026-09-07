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
# Falconer's conjecture on Hausdorff Dimension on compact subsets of ℝᵈ

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Falconer%27s_conjecture)
-/
open MeasureTheory Set

open scoped ENNReal EuclideanGeometry


/-- Falconer's conjecture. -/
@[category research open, AMS 28 42]
lemma Falconer_2d (E : Set <| ℝ^2) (hc : IsCompact E) (hd : 2 < 2 * dimH E ) :
    0 < volume (image2 dist E E) := sorry

/-- Falconer's conjecture. -/
@[category research open, AMS 28 42]
lemma Falconer (d : ℕ) (E : Set <| ℝ^d) (hc : IsCompact E) (hd : d < 2 * dimH E ) :
    0 < volume (image2 dist E E) := sorry
