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
# Interior regularity for the infinity Laplacian

Do bounded infinity-harmonic functions in dimensions $n \ge 3$ satisfy uniform interior
$C^{1,\alpha}$ estimates? This was proved by OpenAI [OAI26].

*References:*
- [OAI26] OpenAI, *Uniform Interior $C^{1,\alpha}$ Estimates for Infinity-Harmonic Functions*,
  OpenAI Math Release preprint (2026).
  [PDF](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/interior-c1-infinity-harmonic.pdf)
- [Ki26] K. Kitamura, *infinity-laplacian-bounded-forcing*, GitHub repository (2026).
  [GitHub](https://github.com/KitaKen1/infinity-laplacian-bounded-forcing)
-/

@[expose] public noncomputable section

namespace InfinityLaplacianFC

/-- The Euclidean distance $|x-y|$ on $\mathbb R^n$. -/
def euclideanDist {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (y i - x i) * (y i - x i))

/-- The viscosity bound $|\Delta_\infty u| \le M$ on $\Omega$: $u$ is continuous,
upper $C^2$ tests satisfy $\Delta_\infty\phi \ge -M$, and lower tests satisfy
$\Delta_\infty\phi \le M$, including tests with zero gradient. -/
def ViscosityBound {n : ℕ} (Ω : Set (Fin n → ℝ))
    (u : (Fin n → ℝ) → ℝ) (M : ℝ) : Prop :=
  ContinuousOn u Ω ∧
    (∀ x ∈ Ω, ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ 2 φ →
      let p : Fin n → ℝ := fun i => (fderiv ℝ φ x) (fun j => if i = j then 1 else 0)
      IsLocalMaxOn (fun y => u y - φ y) Ω x → -M ≤ (fderiv ℝ (fderiv ℝ φ) x) p p) ∧
    (∀ x ∈ Ω, ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ 2 φ →
      let p : Fin n → ℝ := fun i => (fderiv ℝ φ x) (fun j => if i = j then 1 else 0)
      IsLocalMinOn (fun y => u y - φ y) Ω x → (fderiv ℝ (fderiv ℝ φ) x) p p ≤ M)

/-- Uniform interior $C^{1,\alpha}$ regularity for bounded infinity-harmonic functions in
dimension $n \ge 3$: $\|Du\|_{L^\infty(B_{1/2})} + [Du]_{C^{0,\alpha}(B_{1/2})}
\le C\operatorname{osc}_{B_1}u$, with $\alpha \in (0,1/3]$ and $C \ge 0$
depending only on $n$ [OAI26, Theorem 1.1]. -/
@[category research solved, AMS 35,
  formal_proof using lean4 at "https://github.com/KitaKen1/infinity-laplacian-bounded-forcing/blob/1ce77232b98eac4bf4d737b67f2a54478c81d58f/lean/FCSolution.lean#L86"]
theorem infinity_harmonic_regularity :
    ∀ n : ℕ, 3 ≤ n → ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 3 ∧ 0 ≤ C ∧
      ∀ u : (Fin n → ℝ) → ℝ,
        ViscosityBound {x | euclideanDist 0 x < 1} u 0 →
        BddAbove (u '' {x | euclideanDist 0 x < 1}) →
        BddBelow (u '' {x | euclideanDist 0 x < 1}) →
        let D : (Fin n → ℝ) → Fin n → ℝ :=
          fun x i => (fderiv ℝ u x) (fun j => if i = j then 1 else 0)
        (∀ x ∈ {x | euclideanDist 0 x < 1 / 2}, DifferentiableAt ℝ u x) ∧
        (∀ z ∈ {x | euclideanDist 0 x < 1 / 2},
          ∀ x ∈ {x | euclideanDist 0 x < 1 / 2},
          ∀ y ∈ {x | euclideanDist 0 x < 1 / 2}, x ≠ y →
            euclideanDist 0 (D z) +
              euclideanDist (D x) (D y) / (euclideanDist x y) ^ α ≤
              C * (sSup (u '' {x | euclideanDist 0 x < 1}) -
                sInf (u '' {x | euclideanDist 0 x < 1}))) := by
  sorry

/-- A scaling corollary of OpenAI's theorem [OAI26, Theorem 1.1]: for $n \ge 3$ and $R > 0$,
bounded infinity-harmonic functions on $B_R(c)$ are $C^{1,\alpha}$ on $B_{R/2}(c)$ and satisfy
$\|Du\|_\infty + R^\alpha[Du]_\alpha \le C\operatorname{osc}_{B_R(c)}u/R$ there,
with $\alpha \in (0,1/3]$ and $C \ge 0$ depending only on $n$. -/
@[category research solved, AMS 35,
  formal_proof using lean4 at "https://github.com/KitaKen1/infinity-laplacian-bounded-forcing/blob/1ce77232b98eac4bf4d737b67f2a54478c81d58f/lean/FCSolution.lean#L111"]
theorem infinity_harmonic_regularity_rescaled :
    ∀ n : ℕ, 3 ≤ n → ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 3 ∧ 0 ≤ C ∧
      ∀ (u : (Fin n → ℝ) → ℝ) (c : Fin n → ℝ) (R : ℝ), 0 < R →
        ViscosityBound {x | euclideanDist c x < R} u 0 →
        BddAbove (u '' {x | euclideanDist c x < R}) →
        BddBelow (u '' {x | euclideanDist c x < R}) →
        let D : (Fin n → ℝ) → Fin n → ℝ :=
          fun x i => (fderiv ℝ u x) (fun j => if i = j then 1 else 0)
        (∀ x ∈ {x | euclideanDist c x < R / 2}, DifferentiableAt ℝ u x) ∧
        (∀ z ∈ {x | euclideanDist c x < R / 2},
          ∀ x ∈ {x | euclideanDist c x < R / 2},
          ∀ y ∈ {x | euclideanDist c x < R / 2}, x ≠ y →
            euclideanDist 0 (D z) +
              R ^ α * euclideanDist (D x) (D y) /
                (euclideanDist x y) ^ α ≤
              C * ((sSup (u '' {x | euclideanDist c x < R}) -
                sInf (u '' {x | euclideanDist c x < R})) / R)) := by
  sorry

/-- A bounded-forcing variant: for $n \ge 2$, $R > 0$ and $M \ge 0$, bounded continuous
functions satisfying $|\Delta_\infty u| \le M$ in the viscosity sense on $B_R(c)$ are
$C^{1,\alpha}$ on $B_{R/2}(c)$ and satisfy
$\|Du\|_\infty + R^\alpha[Du]_\alpha \le C(\operatorname{osc}_{B_R(c)}u/R + (RM)^{1/3})$
there, with $\alpha \in (0,1/3]$ and $C \ge 0$ depending only on $n$ [Ki26]. -/
@[category research solved, AMS 35,
  formal_proof using lean4 at "https://github.com/KitaKen1/infinity-laplacian-bounded-forcing/blob/1ce77232b98eac4bf4d737b67f2a54478c81d58f/lean/FCSolution.lean#L60"]
theorem bounded_forcing_regularity :
    ∀ n : ℕ, 2 ≤ n → ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 3 ∧ 0 ≤ C ∧
      ∀ (u : (Fin n → ℝ) → ℝ) (c : Fin n → ℝ) (R M : ℝ), 0 < R → 0 ≤ M →
        ViscosityBound {x | euclideanDist c x < R} u M →
        BddAbove (u '' {x | euclideanDist c x < R}) →
        BddBelow (u '' {x | euclideanDist c x < R}) →
        let D : (Fin n → ℝ) → Fin n → ℝ :=
          fun x i => (fderiv ℝ u x) (fun j => if i = j then 1 else 0)
        (∀ x ∈ {x | euclideanDist c x < R / 2}, DifferentiableAt ℝ u x) ∧
        (∀ z ∈ {x | euclideanDist c x < R / 2},
          ∀ x ∈ {x | euclideanDist c x < R / 2},
          ∀ y ∈ {x | euclideanDist c x < R / 2}, x ≠ y →
            euclideanDist 0 (D z) +
              R ^ α * euclideanDist (D x) (D y) /
                (euclideanDist x y) ^ α ≤
              C * ((sSup (u '' {x | euclideanDist c x < R}) -
                sInf (u '' {x | euclideanDist c x < R})) / R + (R * M) ^ (1 / 3 : ℝ))) := by
  sorry

end InfinityLaplacianFC
