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

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.ContinuousOn

/-!
# The Dickman delay differential equation
-/

@[expose] public section

/-- `ρ` is the Dickman–de Bruijn function: it is continuous on `[0, ∞)`, equal to `1` on `[0, 1]`,
and satisfies the delay differential equation `u ρ'(u) = -ρ(u - 1)` for `u > 1`. These conditions
determine `ρ` uniquely on `[0, ∞)`. -/
def IsDickman (ρ : ℝ → ℝ) : Prop :=
  ContinuousOn ρ (Set.Ici 0) ∧ (∀ u ∈ Set.Icc (0 : ℝ) 1, ρ u = 1) ∧
    ∀ u > 1, HasDerivAt ρ (-ρ (u - 1) / u) u
