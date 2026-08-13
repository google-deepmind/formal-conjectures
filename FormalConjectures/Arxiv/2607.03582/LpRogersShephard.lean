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
# Planar $L_p$-Rogers-Shephard, the equality case

*Reference:* [arxiv/2607.03582](https://arxiv.org/abs/2607.03582)
**$L_p$-Rogers-Shephard type inequalities for $L_p$-zonoids and symmetric bodies**
by *Matthieu Fradelizi, Auttawich Manui, Mark Meyer, Cheikh Saliou Ndiaye*

Corollary 29 bounds $|K \oplus_p -K|$ against $|K|$ for planar convex bodies with a centre of
symmetry containing the origin, and notes that parallelograms with a vertex at the origin
attain it. Conjecture 5 asks whether they are the only bodies that do.
-/

open MeasureTheory Real

open scoped EuclideanGeometry

namespace Arxiv.«2607.03582»

/-- The support function $h_K(u) = \sup_{x \in K} \langle x, u\rangle$. -/
noncomputable def supportFunction (K : Set ℝ²) (u : ℝ²) : ℝ := ⨆ x : K, inner ℝ (x : ℝ²) u

/-- The Firey $L_p$-sum $K \oplus_p L$, equation (4) of the source: the body whose support
function is $(h_K^p + h_L^p)^{1/p}$.

The source defines it by that support function, which needs both bodies to contain the origin.
Here it is the intersection of the halfspaces the support function cuts out, which agrees with
the source's set on the bodies the statements below quantify over and needs no separate
existence argument. -/
noncomputable def lpSum (p : ℝ) (K L : Set ℝ²) : Set ℝ² :=
  {x | ∀ u : ℝ², inner ℝ x u ≤ (supportFunction K u ^ p + supportFunction L u ^ p) ^ (1 / p)}

/-- $K$ has a centre of symmetry: some $c$ with $K$ invariant under reflection in $c$. -/
def HasCentreOfSymmetry (K : Set ℝ²) : Prop := ∃ c : ℝ², ∀ x, x ∈ K ↔ (2 • c - x) ∈ K

/-- The constant of Corollary 29, $\frac{2\Gamma(1+1/q)^2}{\Gamma(1+2/q)} + 2$. -/
noncomputable def rsConstant (q : ℝ) : ℝ :=
  2 * Real.Gamma (1 + 1 / q) ^ 2 / Real.Gamma (1 + 2 / q) + 2

/-- $K$ is a parallelogram with a vertex at the origin: the convex hull of $0$, $a$, $b$ and
$a + b$ for linearly independent $a$, $b$. -/
def IsParallelogramAtOrigin (K : Set ℝ²) : Prop :=
  ∃ a b : ℝ², LinearIndependent ℝ ![a, b] ∧ K = convexHull ℝ {0, a, b, a + b}

/--
**Corollary 29 (Fradelizi-Manui-Meyer-Ndiaye, 2026).** For a planar convex body $K$ with a
centre of symmetry containing the origin and $p > 1$,
$$|K \oplus_p -K| \leq \left(\frac{2\Gamma(1+1/q)^2}{\Gamma(1+2/q)} + 2\right)|K|,$$
where $q$ is the Hölder conjugate of $p$.
-/
@[category research solved, AMS 52]
theorem volume_lpSum_le (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K)
    (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K)
    (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1) :
    volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K := by
  sorry

/--
Parallelograms with a vertex at the origin attain the bound, which is the sharpness half of
Corollary 29.
-/
@[category research solved, AMS 52]
theorem volume_lpSum_eq_of_isParallelogramAtOrigin (K : Set ℝ²)
    (hpar : IsParallelogramAtOrigin K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1) :
    volume (lpSum p K (-K)) = ENNReal.ofReal (rsConstant q) * volume K := by
  sorry

/--
**Conjecture 5 (Fradelizi-Manui-Meyer-Ndiaye, 2026).** Among planar convex bodies with a
centre of symmetry containing the origin, for $p > 1$, equality in Corollary 29 holds only for
parallelograms with a vertex at the origin.
-/
@[category research open, AMS 52]
theorem isParallelogramAtOrigin_of_volume_lpSum_eq :
    answer(sorry) ↔ ∀ (K : Set ℝ²), Convex ℝ K → IsCompact K → (interior K).Nonempty →
      HasCentreOfSymmetry K → (0 : ℝ²) ∈ K → ∀ p q : ℝ, 1 < p → 1 / p + 1 / q = 1 →
        volume (lpSum p K (-K)) = ENNReal.ofReal (rsConstant q) * volume K →
          IsParallelogramAtOrigin K := by
  sorry

/-- At $p = 2$ the conjugate is also $2$, and $\Gamma(3/2)^2 / \Gamma(2) = \pi/4$, so the
constant is $\pi/2 + 2$. -/
@[category API, AMS 52]
theorem rsConstant_two : rsConstant 2 = π / 2 + 2 := by
  have h1 : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  have h2 : (1 : ℝ) + 2 / 2 = 2 := by norm_num
  rw [rsConstant, h1, h2, Real.Gamma_two]
  rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  have : Real.sqrt π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  nlinarith [this, Real.pi_pos]

end Arxiv.«2607.03582»
