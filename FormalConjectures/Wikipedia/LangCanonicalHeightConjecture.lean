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
# Lang's canonical height lower bound conjecture

Given an algebraic number field $K$ and an elliptic curve $E / K$, the Néron–Tate canonical
height $\hat{h} : E(K) \to \mathbb{R}$ defines a nonnegative quadratic form over $E(K)$
that vanishes precisely at points of finite order.

Serge Lang conjectured a uniform positive lower bound on $\hat{h}(P)$ for non-torsion points
$P \in E(K)$ in terms of the minimal discriminant ideal $\mathfrak{D}_{E/K}$ and the logarithmic
height of the $j$-invariant $j(E)$ (originally stated over $\mathbb{Q}$ in terms of
$|\Delta_{\min}(E)|$ in [La78], p. 92, and extended to number fields with Joseph H. Silverman
[Si81], [HS88]). Marc Hindry and Silverman proved the bound over function fields of characteristic
zero and deduced the number-field case conditionally from the $abc$ / Szpiro conjecture [HS88].

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/N%C3%A9ron%E2%80%93Tate_height)
- [La78] S. Lang, *Elliptic Curves: Diophantine Analysis*, Grundlehren der mathematischen
  Wissenschaften 231, Springer-Verlag, Berlin, 1978, p. 92.
- [La97] S. Lang, *Survey of Diophantine Geometry*, Springer-Verlag, Berlin, 1997, pp. 73–74.
- [Si81] J. H. Silverman, *Lower bound for the canonical height on elliptic curves*, Duke Math. J.
  48 (1981), no. 3, 633–648.
- [HS88] M. Hindry and J. H. Silverman, *The canonical height and integral points on elliptic
  curves*, Invent. Math. 93 (1988), no. 2, 419–450.
-/

@[expose] public section

namespace LangCanonicalHeightConjecture

open WeierstrassCurve WeierstrassCurve.Affine.Point

/-- The naive $x$-coordinate logarithmic height is nonnegative at every rational point. -/
@[category API, AMS 11 14]
theorem naiveHeight_nonneg {K : Type*} [DecidableEq K] [Field K] [Height.AdmissibleAbsValues K]
    {W : WeierstrassCurve.Affine K} (P : W.Point) :
    0 ≤ P.naiveHeight := by
  cases P with
  | zero => simp [WeierstrassCurve.Affine.Point.naiveHeight]
  | some => exact Height.zero_le_logHeight₁ _

/-- At the identity point $0 \in E(K)$, `canonicalHeight` vanishes. -/
@[category test, AMS 11 14]
theorem canonicalHeight_zero {K : Type*} [DecidableEq K] [Field K] [Height.AdmissibleAbsValues K]
    (W : WeierstrassCurve.Affine K) :
    (0 : W.Point).canonicalHeight = 0 := by
  unfold WeierstrassCurve.Affine.Point.canonicalHeight
  have h0 : (fun n : ℕ ↦ (2 ^ n • (0 : W.Point)).naiveHeight / (4 : ℝ) ^ n) = fun _ ↦ 0 := by
    ext n
    rw [nsmul_zero]
    change (0 : ℝ) / (4 : ℝ) ^ n = 0
    simp
  rw [h0, tendsto_const_nhds.limUnder_eq]

/-- **Néron–Tate Torsion Characterization**: For any number field $K$ together with an elliptic
curve $W / K$, a point $P \in W(K)$ has canonical height $0$ if and only if $P$ has finite additive
order. -/
@[category textbook, AMS 11 14]
theorem canonicalHeight_eq_zero_iff_isOfFinAddOrder {K : Type*} [Field K] [NumberField K]
    [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (P : W.toAffine.Point) :
    P.canonicalHeight = 0 ↔ IsOfFinAddOrder P := by
  sorry

/-- **Lang's Canonical Height Conjecture** ([La97], pp. 73–74; [HS88], Introduction): For every
algebraic number field $K$, there exists a constant $c > 0$ depending only on $K$ such that for
every elliptic curve $W / K$ and every non-torsion point $P \in W(K)$,
$$\hat{h}(P) \ge c \max\bigl\{1,\, \log N_{K/\mathbb{Q}}(\mathfrak{D}_{W/K}),\, h_K(j(W))\bigr\}.$$

Note: Wikipedia writes $\log\max\{\operatorname{Norm}_{K/\mathbb{Q}}\operatorname{Disc}(E/K),
h(j(E))\}$, mixing the multiplicative ideal norm with the logarithmic height $h(j(E))$. Following
[HS88], Introduction, we place both on the relative logarithmic scale (`Height.logHeight₁`) and
include $1$ in the maximum so the lower bound remains positive when $\mathfrak{D}_{W/K} = (1)$ and
$h_K(j(W)) = 0$. Note also that `WeierstrassCurve.Affine.Point.canonicalHeight` uses the BSD
normalization (twice the classical $\hat{h}$), which rescales $c$ by $2$. -/
@[category research open, AMS 11 14]
theorem lang_canonical_height_conjecture (K : Type*) [Field K] [NumberField K] [DecidableEq K] :
    ∃ c : ℝ, 0 < c ∧
      ∀ (W : WeierstrassCurve K) [W.IsElliptic] (P : W.toAffine.Point),
        ¬ IsOfFinAddOrder P →
          c * max 1 (max (Real.log (W.minimalDiscriminant.absNorm : ℝ)) (Height.logHeight₁ W.j)) ≤
            P.canonicalHeight := by
  sorry

/-- **Lang's Original Minimal-Discriminant Conjecture over $\mathbb{Q}$** ([La78], p. 92): Some
universal constant $c > 0$ satisfies, for every elliptic curve $W / \mathbb{Q}$ and every
non-torsion point $P \in W(\mathbb{Q})$,
$$\hat{h}(P) \ge c \log |\Delta_{\min}(W)|.$$
Over $\mathbb{Q}$, every elliptic curve satisfies $|\Delta_{\min}(W)| \ge 11$, so
$\log |\Delta_{\min}(W)| > 1$ without needing $\max(1, \cdot)$. -/
@[category research open, AMS 11 14]
theorem lang_canonical_height_conjecture.variants.rat_minimal_discriminant :
    ∃ c : ℝ, 0 < c ∧
      ∀ (W : WeierstrassCurve ℚ) [W.IsElliptic] (P : W.toAffine.Point),
        ¬ IsOfFinAddOrder P →
          c * Real.log (W.minimalDiscriminant.absNorm : ℝ) ≤ P.canonicalHeight := by
  sorry

end LangCanonicalHeightConjecture
