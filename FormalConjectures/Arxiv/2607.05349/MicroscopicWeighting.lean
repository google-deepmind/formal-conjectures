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
# The microscopic weighting on a metric space

*Reference:* [arxiv/2607.05349](https://arxiv.org/abs/2607.05349)
**The microscopic weighting on a metric space**
by *Emily Roff, Simon Willerton*
-/

open Filter Matrix

open scoped Topology

namespace Arxiv.«2607.05349»

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [MetricSpace X]

/-- The similarity matrix $Z(t)_{ij} = e^{-t\,d(x_i, x_j)}$ of a finite metric space. -/
noncomputable def similarityMatrix (X : Type*) [Fintype X] [MetricSpace X] (t : ℝ) :
    Matrix X X ℝ :=
  Matrix.of fun i j => Real.exp (-t * dist i j)

/-- The distance matrix $D_{ij} = d(x_i, x_j)$ of a finite metric space. -/
noncomputable def distanceMatrix (X : Type*) [Fintype X] [MetricSpace X] : Matrix X X ℝ :=
  Matrix.of fun i j => dist i j

/-- The weighting $\vec{w}(t) = Z(t)^{-1}\mathbf{1}$ at scale `t`.

`Matrix.inv` is `0` on singular matrices, so this is only the intended vector where `Z t` is
invertible. That is enough here: `Z 0` is the all-ones matrix and `Z` is continuous, so `Z t`
is invertible for all small enough `t > 0`, which is where the limit below is taken. -/
noncomputable def weighting (X : Type*) [Fintype X] [DecidableEq X] [MetricSpace X] (t : ℝ) :
    X → ℝ :=
  (similarityMatrix X t)⁻¹ *ᵥ 1

/-- `X` admits a *microscopic weighting* when $\vec{w}(t)$ converges as $t \to 0^+$. -/
def HasMicroscopicWeighting (X : Type*) [Fintype X] [DecidableEq X] [MetricSpace X] : Prop :=
  ∃ w : X → ℝ, Tendsto (weighting X) (𝓝[>] 0) (𝓝 w)

/-- `g` is a *gauging* for `M` with concentration `c`: it sums to `1` and `M g` is the constant
vector `c`. This is Definition 2.3 of the source, which states it for symmetric `M`. -/
def IsGauging (M : Matrix X X ℝ) (g : X → ℝ) (c : ℝ) : Prop :=
  ∑ i, g i = 1 ∧ M *ᵥ g = Function.const X c

omit [DecidableEq X] [Nonempty X] [MetricSpace X] in
/-- All gaugings of a symmetric matrix share one concentration, so $\mathrm{con}$ is an
attribute of the matrix. The source records this after Definition 2.3, as the calculation
$c = c\mathbf{1}^T v' = (v^TA^T)v' = v^T(c'\mathbf{1}) = c'$, and Definition 2.4 rests on it. -/
@[category textbook, AMS 15]
theorem concentration_unique {M : Matrix X X ℝ} (hM : M.IsSymm) {g g' : X → ℝ} {c c' : ℝ}
    (h : IsGauging M g c) (h' : IsGauging M g' c') : c = c' := by
  obtain ⟨hs, hg⟩ := h
  obtain ⟨hs', hg'⟩ := h'
  have key : g' ⬝ᵥ (M *ᵥ g) = (M *ᵥ g') ⬝ᵥ g := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hM.eq]
  rw [hg, hg'] at key
  simpa [dotProduct, Function.const, ← Finset.sum_mul, ← Finset.mul_sum, hs, hs'] using key

/-- `M` has finite concentration, written $\mathrm{con}(M) \neq \infty$ in the source: some
gauging for `M` exists.

Definition 2.4 sets $\mathrm{con}(M)$ to the concentration of any gauging, and to $\infty$ when
there is none, so `con(M) ≠ ∞` is exactly this. Stating it as existence keeps the value of
$\mathrm{con}$ out of the statement; `concentration_unique` above is what makes that value
well defined in the first place. -/
def HasFiniteConcentration (M : Matrix X X ℝ) : Prop :=
  ∃ g c, IsGauging M g c

/--
**Conjecture 3.3 (Roff-Willerton, 2026).** A finite metric space admits a microscopic weighting
if and only if its distance matrix has finite concentration.

`Nonempty` is needed and not just tidiness. On the empty space every gauging condition fails,
since `∑ i, g i` is `0` rather than `1`, while `X → ℝ` is a subsingleton so the weighting
converges trivially. The equivalence would be false there for reasons that have nothing to do
with the question.
-/
@[category research open, AMS 15 51]
theorem microscopic_weighting_iff_finite_concentration :
    answer(sorry) ↔ ∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X] [MetricSpace X],
      HasMicroscopicWeighting X ↔ HasFiniteConcentration (distanceMatrix X) := by
  sorry

/--
One direction is known: a microscopic weighting implies finite concentration (Theorem 3.1(3)).
Together with the conjecture above this leaves the converse, that finite concentration is enough.
-/
@[category research solved, AMS 15 51]
theorem hasFiniteConcentration_of_hasMicroscopicWeighting
    (h : HasMicroscopicWeighting X) : HasFiniteConcentration (distanceMatrix X) := by
  sorry

/--
Theorem 3.8: the conjecture is known when the distance matrix is invertible, and the microscopic
weighting is then the unique gauging.
-/
@[category research solved, AMS 15 51]
theorem hasMicroscopicWeighting_iff_of_isUnit (h : IsUnit (distanceMatrix X).det) :
    HasMicroscopicWeighting X ↔ HasFiniteConcentration (distanceMatrix X) := by
  sorry

end Arxiv.«2607.05349»
