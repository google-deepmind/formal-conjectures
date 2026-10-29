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
# Convexity of Fisher information along the heat flow

Can the functional $\mathcal{D}[f]$ be negative for an admissible density $f$? Equivalently, is
the Fisher information of the Gaussian heat flow always convex in time? This is Problem (iii) of
[ZFGW26, Section 7.3]; it is known in dimensions $d \le 4$ and left open for $d \ge 5$
[ZFGW26, Section 7.2].

References:
- [ZFGW26] J. Zou, L. Fan, J. Gao and J. Wang, *A Hexagonal Counterexample to Log-Convexity of
  Fisher Information Along the Heat Flow*, arXiv:2605.18081 (2026).
  https://arxiv.org/abs/2605.18081
- [Ki26] K. Kitamura, *Fisher information along the heat flow is not convex*, Lean 4
  formalization (2026),
  [GitHub repository](https://github.com/KitaKen1/fisher-information-nonconvexity/tree/a6ff274a04e5b6d813b6f06dc62d3d68a21ae31a).
-/

@[expose] public section

open MeasureTheory Real
open scoped ContDiff SchwartzMap

namespace Arxiv.«2605.18081»

/-- The heat flow $f * \gamma_t$, where $\gamma_t$ is the Gaussian density of variance $t$. -/
noncomputable def heatFlow {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ y, f y * ((2 * π * t) ^ (-(d : ℝ) / 2) * exp (-‖x - y‖ ^ 2 / (2 * t)))

/-- The Fisher information $\int |\nabla \log \rho|^2 \rho$. -/
noncomputable def fisherInformation {d : ℕ} (ρ : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ∫ x, ‖fderiv ℝ (fun y => log (ρ y)) x‖ ^ 2 * ρ x

/-- The entries $H_{ij} = -\partial_i \partial_j \log f$ of the negative log-Hessian. -/
noncomputable def negLogHess {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (i j : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -fderiv ℝ (fun y => fderiv ℝ (fun z => log (f z)) y (EuclideanSpace.single i 1)) x
    (EuclideanSpace.single j 1)

/-- The admissible densities of [ZFGW26, Section 7]: positive Schwartz probability densities with
$\mathcal{I}[f], \mathcal{Q}[f], \mathcal{D}[f] < \infty$ and $\mathcal{Q}[f] > 0$, where
$\mathcal{Q}[f] = \int \operatorname{tr}(H^2) f$ and
$\mathcal{D}[f] = \int (|\nabla H|^2 + 2 \operatorname{tr} H^3) f$. -/
def IsAdmissible {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  (∃ φ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ), ⇑φ = f) ∧ (∀ x, 0 < f x) ∧ ∫ x, f x = 1 ∧
    Integrable (fun x => ‖fderiv ℝ (fun y => log (f y)) x‖ ^ 2 * f x) ∧
    Integrable (fun x => (∑ i, ∑ j, negLogHess f i j x ^ 2) * f x) ∧
    Integrable (fun x => ((∑ i, ∑ j, ∑ k,
        fderiv ℝ (negLogHess f i j) x (EuclideanSpace.single k 1) ^ 2) +
      2 * ∑ i, ∑ j, ∑ k, negLogHess f i j x * negLogHess f j k x * negLogHess f k i x) * f x) ∧
    0 < ∫ x, (∑ i, ∑ j, negLogHess f i j x ^ 2) * f x

/-- The class of the variant: smooth positive probability densities with finite Fisher
information. Compared with `IsAdmissible`, the Schwartz condition is replaced by smoothness, and
the conditions on $\mathcal{Q}$ and $\mathcal{D}$ are dropped. -/
def IsWeaklyAdmissible {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ (∀ x, 0 < f x) ∧ ∫ x, f x = 1 ∧
    Integrable (fun x => ‖fderiv ℝ (fun y => log (f y)) x‖ ^ 2 * f x)

set_option linter.style.formal_proof_palomar false in
/-- Is the Fisher information convex along the heat flow for every admissible density
[ZFGW26, Section 7.3, Problem (iii)]? The answer is no [Ki26]. -/
@[category research solved, question, AMS 35 60,
    formal_proof using lean4 at "https://github.com/KitaKen1/fisher-information-nonconvexity/blob/fe6ade9846c53e5cb0dcbc00eca359c83f8d0f55/lean/Fisher41/FC/Main.lean#L37"]
theorem fisherInformationConvexity :
    ¬ ∀ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), IsAdmissible f →
      ConvexOn ℝ (Set.Ioi 0) (fun t => fisherInformation (heatFlow f t)) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- The same question for every smooth positive probability density with finite Fisher
information. The answer is no [Ki26]. -/
@[category research solved, question, AMS 35 60,
    formal_proof using lean4 at "https://github.com/KitaKen1/fisher-information-nonconvexity/blob/fe6ade9846c53e5cb0dcbc00eca359c83f8d0f55/lean/Fisher41/FC/Main.lean#L48"]
theorem fisherInformationConvexity.variants.smooth :
    ¬ ∀ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), IsWeaklyAdmissible f →
      ConvexOn ℝ (Set.Ioi 0) (fun t => fisherInformation (heatFlow f t)) := by
  sorry

end Arxiv.«2605.18081»
