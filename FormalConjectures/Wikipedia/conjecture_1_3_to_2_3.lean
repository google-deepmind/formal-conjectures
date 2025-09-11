/-
Copyright 2025 Google LLC

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

-- https://en.wikipedia.org/wiki/1/3%E2%80%932/3_conjecture
import FormalConjectures.Util.ProblemImports

/--
Does every finite partially ordered set that is not totally ordered
contain two elements x and y such that the probability that
x appears before y in a random linear extension is between 1/3 and 2/3?

The set of all total order extensions is represented here
as monotone bijections P -> 1..n
-/
@[open_problem]
theorem conjecture_1_3_to_2_3 (P : Type) [Finite P] [PartialOrder P]
    (not_total : ¬ IsTotal P (· ≤ ·)) (total_ext : Set (P ↪o ℕ))
    (total_ext_def : ∀ σ, σ ∈ total_ext ↔ Set.range σ = Set.Icc 1 (Nat.card P)) :
    ∃ x y : P, ({σ ∈ total_ext | σ x < σ y}.ncard / total_ext.ncard : ℚ)
      ∈ Set.Icc (1/3) (2/3) := sorry
