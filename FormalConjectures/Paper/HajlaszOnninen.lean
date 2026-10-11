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
# Endpoint gradient bound for the centered ball maximal operator

[HO04, Question 1] is the main statement. The homogeneous estimate for
$d \ge 2$ is a variant. The one-dimensional case is [K15, Corollary 1.4].

*References:* [HO04] P. Hajlasz and J. Onninen, *On boundedness of maximal functions
in Sobolev spaces*, Ann. Acad. Sci. Fenn. Math. 29 (2004), 167--176,
Question 1, p. 169.
https://sites.pitt.edu/~hajlasz/OriginalPublications/HajlaszO-OnBoundedness-AnnAcadSciFennMath-29-1994-167-176.pdf#page=3

[K15] O. Kurka, *On the variation of the Hardy--Littlewood maximal function*,
Ann. Acad. Sci. Fenn. Math. 40 (2015), 109--133, Corollary 1.4.
https://www.acadsci.fi/mathematica/Vol40/vol40pp109-133.pdf#page=2

[Ki26] K. Kitamura, *Centered ball maximal endpoint*, Lean 4 proof, 2026.
https://github.com/KitaKen1/centered-ball-maximal-endpoint/tree/fb93537ea35f8e9c2deb8c70fc314ef3792030ae
-/

@[expose] public section

noncomputable section

namespace CenteredBallMaximal

open MeasureTheory Set Metric
open scoped ENNReal ContDiff InnerProductSpace

/-- G is the weak gradient of f. -/
def HasWeakGradient {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  LocallyIntegrable f volume ∧ LocallyIntegrable G volume ∧
    ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ v : EuclideanSpace ℝ (Fin d),
        (∫ x, f x * fderiv ℝ φ x v) = -∫ x, φ x * ⟪G x, v⟫_ℝ

/-- The centered ball maximal function. -/
def maximal {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r),
    (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ENNReal.ofReal |f y|

/-- [HO04, Question 1]: is $f \mapsto |\nabla Mf|$ bounded from
$W^{1,1}$ to $L^1$ in every $d \ge 1$?
The answer is positive. See [Ki26]. -/
@[category research solved, AMS 42 46,
    formal_proof using lean4 at "https://github.com/KitaKen1/centered-ball-maximal-endpoint/blob/fb93537ea35f8e9c2deb8c70fc314ef3792030ae/lean/CenteredBallMaximal/Main.lean#L48"]
theorem endpointGradientBound :
    answer(True) ↔
      ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ)
          (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
          (Integrable f volume ∧ Integrable G volume ∧ HasWeakGradient f G) →
          (∀ᵐ x ∂volume, maximal f x < (∞ : ℝ≥0∞)) ∧
            ∃ H : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
              HasWeakGradient (fun x => (maximal f x).toReal) H ∧ Integrable H volume ∧
                (∫ x, ‖H x‖) ≤ C * ((∫ x, |f x|) + ∫ x, ‖G x‖) := by
  sorry

/-- Homogeneous variant of [HO04, Question 1] in every $d \ge 2$.
The answer is positive. See [Ki26]. -/
@[category research solved, AMS 42 46,
    formal_proof using lean4 at "https://github.com/KitaKen1/centered-ball-maximal-endpoint/blob/fb93537ea35f8e9c2deb8c70fc314ef3792030ae/lean/CenteredBallMaximal/Main.lean#L32"]
theorem endpointGradientBound_homogeneous :
    answer(True) ↔
      ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ)
          (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
          (Integrable f volume ∧ Integrable G volume ∧ HasWeakGradient f G) →
          (∀ᵐ x ∂volume, maximal f x < (∞ : ℝ≥0∞)) ∧
            ∃ H : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
              HasWeakGradient (fun x => (maximal f x).toReal) H ∧ Integrable H volume ∧
                (∫ x, ‖H x‖) ≤ C * ∫ x, ‖G x‖ := by
  sorry

end CenteredBallMaximal
