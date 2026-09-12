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

/-!
# Erdős Problem 1045

*References:*
- [erdosproblems.com/1045](https://www.erdosproblems.com/1045)
- [EHP58] Erdős, P. and Herzog, F. and Piranian, G., *Metric properties of polynomials*.
  J. Analyse Math. (1958), 125-148.
- [Po61] Pommerenke, Ch., *On metric properties of complex polynomials*. Michigan Math. J.
  (1961), 97-115.
-/

open Complex

namespace Erdos1045

/--
The quantity $\Delta(z_1,\ldots,z_n)=\prod_{i\neq j}\lvert z_i-z_j\rvert$.
-/
noncomputable def delta {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖

/-- The points $z_1,\ldots,z_n$ satisfy $\lvert z_i-z_j\rvert\leq 2$ for all $i,j$. -/
def DiameterLETwo {n : ℕ} (z : Fin n → ℂ) : Prop :=
  ∀ i j, ‖z i - z j‖ ≤ 2

/--
The points $z_1,\ldots,z_n$ are the vertices of a regular $n$-gon (labelled in cyclic order).
-/
def IsRegularPolygonVertices {n : ℕ} (z : Fin n → ℂ) : Prop :=
  ∃ (c : ℂ) (r θ : ℝ), ∀ i : Fin n,
    z i = c + r • exp (I * (θ + 2 * Real.pi * (i : ℝ) / n))

/-- $\Delta$ of a single point is $1$. -/
@[category test, AMS 32 51]
theorem delta_one (z : Fin 1 → ℂ) : delta z = 1 := by
  simp [delta]

/--
Let $z_1,\ldots,z_n\in \mathbb{C}$ with $\lvert z_i-z_j\rvert\leq 2$ for all $i,j$, and
$$\Delta(z_1,\ldots,z_n)=\prod_{i\neq j}\lvert z_i-z_j\rvert.$$
What is the maximum possible value of $\Delta$?

A problem of Erdős, Herzog, and Piranian [EHP58, p.143].
-/
@[category research open, AMS 32 51]
theorem erdos_1045 (n : ℕ) :
    IsGreatest {delta z | (z : Fin n → ℂ) (_ : DiameterLETwo z)} answer(sorry) := by
  sorry

/--
Is $\Delta$ maximised by taking the $z_i$ to be the vertices of a regular polygon?

Hu and Tang found counterexamples for $n=4$ and $n=6$, and Cambie showed that a regular
$n$-gon is not a maximiser for even $n\geq 4$. It remains possible that a regular $n$-gon
is a maximiser for odd $n$.
-/
@[category research open, AMS 32 51]
theorem erdos_1045.variants.regular_polygon : answer(sorry) ↔
    ∀ n : ℕ, ∃ z : Fin n → ℂ, IsRegularPolygonVertices z ∧ DiameterLETwo z ∧
      IsGreatest {delta w | (w : Fin n → ℂ) (_ : DiameterLETwo w)} (delta z) := by
  sorry

end Erdos1045
