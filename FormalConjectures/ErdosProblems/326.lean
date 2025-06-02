/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 326

*Reference:* [erdosproblems.com/326](https://www.erdosproblems.com/326)
-/

open Filter

open scoped Topology

/--
Let $A \subset \mathbb{N}$ be an additive basis of order 2.

Must there exist $B = \{b_1 < b_2 < \dots\} \subseteq A$ which is also a basis such that
$\lim_{k\to\infty} \frac{b_k}{k^2}$ does not exist?
-/
@[category research open, AMS 5, AMS 11]
theorem erdos_326 : (∀ (A : Set ℕ), A.IsAddBasisOfOrder 2 →
    ∃ (b : ℕ → ℕ), StrictMono b ∧ ∀ n, b n ∈ A ∧ (Set.range b).IsAddBasis ∧
      ∀ (x : ℝ), ¬ Tendsto (fun n ↦ (b n : ℝ) / n ^ 2) atTop (𝓝 x)) ↔ answer(sorry) := by
  sorry

/--
Erdős originally asked whether this was true with `A = B`, but this was disproved by Cassels.
-/
@[category research solved, AMS 5, AMS 11]
theorem erdos_326.variants.eq : (∀ (A : Set ℕ), A.IsAddBasisOfOrder 2 →
    ∃ (a : ℕ → ℕ), StrictMono a ∧ Set.range a = A ∧
      ∀ (x : ℝ), ¬ Tendsto (fun n ↦ (a n : ℝ) / n ^ 2) atTop (𝓝 x)) ↔ answer(False) := by
  sorry
