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
import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Erdős Problem 1041

*Reference:* [erdosproblems.com/1041](https://www.erdosproblems.com/1041)
-/

open Polynomial MeasureTheory ENNReal

namespace Erdos1041

variable (n : ℕ) (f : ℂ[X])

noncomputable def numRoots (f : ℂ[X]) : ℕ := Multiset.card f.roots

/--
The length of a subset $s$ of $\mathbb{C}$ is defined to be its 1-dimensional
Hausdorff measure $\mathcal{H}^1(s)$.
-/
noncomputable def length (s : Set ℂ) : ℝ≥0∞ := μH[1] s

variable {α : Type _} [TopologicalSpace α]

/-- The set of connected components of a subset of a topological space. -/
def connectedComponents (s : Set α) : Set (Set α) :=
  {t | t ⊆ s ∧ IsConnected t ∧ ∀ u, t ⊂ u → u ⊆ s → ¬IsConnected u}

/--
**Erdős–Herzog–Piranian Component Lemma** (Metric Properties of Polynomials, 1958):
If $f$ is a degree $n$ polynomial with all roots in the unit disk,
then some connected component
of $\{z \mid |f(z)| < 1\}$ contains at least two distinct roots.
-/
@[category research solved, AMS 32]
theorem exists_connected_component_contains_two_roots
    (h : ∀ z, z ∈ f.rootSet ℂ → ‖z‖ < 1) (hn : numRoots f = n) :
  ∃ (s : Set ℂ) (z₁ z₂ : ℂ),
    s ∈ connectedComponents {z | ‖f.eval z‖ < 1} ∧
    z₁ ≠ z₂ ∧ z₁ ∈ f.rootSet ℂ ∧ z₂ ∈ f.rootSet ℂ ∧ z₁ ∈ s ∧ z₂ ∈ s := by
  sorry

/--
Let
$$ f(z) = \prod_{i=1}^{n} (z - z_i) \in \mathbb{C}[x] $$
with $|z_i| < 1$ for all $i$.

Conjecture: Must there always exist a path of length less than 2 in
$$ \{ z \in \mathbb{C} \mid |f(z)| < 1 \} $$
which connects two of the roots of $f$?
-/
@[category research open, AMS 32]
theorem erdos_1041
    (h : ∀ z, z ∈ f.rootSet ℂ → ‖z‖ < 1) (hn : numRoots f = n) :
  ∃ (z₁ z₂ : ℂ) (hz : z₁ ≠ z₂) (hz₁ : z₁ ∈ f.rootSet ℂ)
    (hz₂ : z₂ ∈ f.rootSet ℂ) (γ : Path z₁ z₂),
    Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧
    length (Set.range γ) < 2 := by
  sorry

end Erdos1041
