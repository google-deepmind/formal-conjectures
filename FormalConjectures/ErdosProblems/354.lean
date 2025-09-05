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

# Erdős Problem 354
*Reference:* [erdosproblems.com/354](https://www.erdosproblems.com/354)

-/
namespace Erdos354

/-- The set `{⌊a⌋, ⌊2 * a⌋, ⌊4 * a⌋, ...}`. -/
def FloorMultiples (a γ : ℝ) : Set ℝ := Set.range (fun (n : ℕ) ↦ ⌊γ ^ n * a⌋)

/-- Let $\alpha,\beta\in \mathbb{R}_{>0}$ such that $\alpha/\beta$ is irrational. Is
\[\{ \lfloor \alpha\rfloor,\lfloor 2\alpha\rfloor,\lfloor 4\alpha\rfloor,\ldots\}\cup
\{ \lfloor \beta\rfloor,\lfloor 2\beta\rfloor,\lfloor 4\beta\rfloor,\ldots\}\] complete?-/
@[category research open, AMS 11]
theorem erdos_354.parts.i : (∀ᵉ (α > 0) (β > 0), Irrational (α / β) →
    IsAddComplete (FloorMultiples α 2 ∪ FloorMultiples β 2)) ↔ answer(sorry) := by
  sorry

/-- Let $\alpha,\beta\in \mathbb{R}_{>0}$ such that $\alpha/\beta$ is irrational. Is
\[\{ \lfloor \alpha\rfloor,\lfloor \gamma\alpha\rfloor,\lfloor \gamma^2\alpha\rfloor,\ldots\}\cup
\{ \lfloor \beta\rfloor,\lfloor \gamma\beta\rfloor,\lfloor \gamma^2\beta\rfloor,\ldots\}\] complete? -/
@[category research open, AMS 11]
theorem erdos_354.parts.ii : (∃ γ ∈ Set.Ioo 1 2, ∀ᵉ (α > 0) (β > 0), Irrational (α / β) →
    IsAddComplete (FloorMultiples α γ ∪ FloorMultiples β γ)) ↔ answer(sorry) := by
  sorry

end Erdos354
