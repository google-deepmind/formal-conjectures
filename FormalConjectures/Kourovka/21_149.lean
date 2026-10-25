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
# Conjecture 21.149

by A. V. Zenkov

The problem is due to V. M. Kopytov and N. Ya. Medvedev. Its original form asked for an order
automorphism of a Dlab group that is not inner (`kourovka_21_149.variants.not_inner`). After that
form was solved, the problem was revised to the stronger question below [vDJMM, Appendix A].
[GYZ] answered the revised question for order-preserving embeddings and rank-one slope groups.

The Notebook does not define Dlab groups. We follow [Dl] and [GYZ]: the Dlab groups with slope
group $H$ are four groups of order automorphisms of $I = [0, 1]$ and two groups of order
automorphisms of the extended real line $\overline{\mathbb{R}}$. All six are viewed as subgroups
of the order automorphisms of $\mathbb{R}$ (`IsDlabGroup`).

*References:*
- [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v46), Problem 21.149. The original
  wording is in [arXiv:1401.0300v43](https://arxiv.org/abs/1401.0300v43).
- [GYZ] T. Gong, Y. Yang and M. R. Zeng, *An order automorphism of a Dlab group not induced by
  conjugation*, [arXiv:2609.18630](https://arxiv.org/abs/2609.18630).
- [vDJMM] W. van Doorn, E. Judin, P. Monticone and D. Morrison,
  [arXiv:2607.17477](https://arxiv.org/abs/2607.17477).
- [Dl] V. Dlab, *On a family of simple ordered groups*, J. Austral. Math. Soc. 8 (1968), 591–608.
-/

@[expose] public section

open Filter Topology

namespace Kourovka.«21.149»

/--
An order automorphism $f$ of $\mathbb{R}$ is *locally right $H$-linear* if every point has a
right neighbourhood on which $f$ is affine with slope in $H \le \mathbb{R}_{>0}$.
-/
def IsLocallyRightLinear (H : Subgroup NNRealˣ) (f : ℝ ≃o ℝ) : Prop :=
  ∀ a : ℝ, ∃ ε > (0 : ℝ), ∃ h ∈ H, ∀ x : ℝ, a < x → x < a + ε →
    f x = f a + ((h : NNReal) : ℝ) * (x - a)

/--
$A$ is one of the six Dlab groups with slope group $H$. Each consists of the locally right
$H$-linear order automorphisms $f$ with a condition at the ends.

- Four act on $I = [0, 1]$. An order automorphism of $I$ is identified with its extension to
  $\mathbb{R}$ by the identity, so $f$ fixes every point outside $(0, 1)$. The four groups are
  $D_H(I)$ ($f$ is also the identity near $0$ and near $1$), $D_{H*}(I)$ (near $0$),
  $D_{*H}(I)$ (near $1$) and $\overline{D}_H(I)$ (no further condition).
- Two act on the extended real line $\overline{\mathbb{R}}$, whose order automorphisms are those
  of $\mathbb{R}$. They are $D_H$ ($f$ is the identity near $-\infty$ and near $+\infty$) and
  $D_{H*}$ (near $-\infty$).
-/
def IsDlabGroup (H : Subgroup NNRealˣ) (A : Subgroup (ℝ ≃o ℝ)) : Prop :=
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∧
    (∀ᶠ x in 𝓝 (0 : ℝ), f x = x) ∧ ∀ᶠ x in 𝓝 (1 : ℝ), f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∧
    ∀ᶠ x in 𝓝 (0 : ℝ), f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∧
    ∀ᶠ x in 𝓝 (1 : ℝ), f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ ∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ᶠ x in atBot, f x = x) ∧
    ∀ᶠ x in atTop, f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ ∀ᶠ x in atBot, f x = x)

/--
Dlab's order on a group $G$ of order automorphisms of $\mathbb{R}$: $f < g$ if $f(x) < g(x)$ at
some point $x$ and every point $y$ with $g(y) < f(y)$ lies to the right of $x$. For elements of
a Dlab group, this says that $f$ is below $g$ just after the point where they start to differ.
-/
def DlabLt {G : Subgroup (ℝ ≃o ℝ)} (f g : G) : Prop :=
  ∃ x, (f : ℝ ≃o ℝ) x < (g : ℝ ≃o ℝ) x ∧ ∀ y, (g : ℝ ≃o ℝ) y < (f : ℝ ≃o ℝ) y → x < y

/--
Are there order automorphisms of Dlab groups that are not induced by conjugation by elements of
a (possibly bigger) Dlab group?

A Dlab group $G$ (on $I$ or on $\overline{\mathbb{R}}$) carries Dlab's order, and $\alpha$ is an
automorphism of $G$ that preserves it. The automorphism $\alpha$ is induced by conjugation in a
bigger Dlab group $A$ if $G$ embeds into $A$ by an injective homomorphism $e$ and some $u \in A$
satisfies $e(\alpha(f)) = u^{-1} e(f) u$ for all $f \in G$. This includes the inclusions and the
order-preserving embeddings of [GYZ]. The slope groups are arbitrary.
-/
@[category research solved, question, AMS 6 20,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/kourovka-21-149-lean/blob/5c34c22661071d412f66a42009a1fe68db473b31/lean/Kourovka21149FC.lean#L5740-L5775"]
theorem kourovka_21_149 :
    ∃ (K : Subgroup NNRealˣ) (G : Subgroup (ℝ ≃o ℝ)), IsDlabGroup K G ∧
      ∃ α : G ≃* G, (∀ f g : G, DlabLt (α f) (α g) ↔ DlabLt f g) ∧
        ¬ ∃ (H : Subgroup NNRealˣ) (A : Subgroup (ℝ ≃o ℝ)), IsDlabGroup H A ∧
          ∃ e : G →* A, Function.Injective e ∧ ∃ u : A, ∀ f : G, e (α f) = u⁻¹ * e f * u := by
  sorry

/--
The original form of the problem: are there order automorphisms of Dlab groups that are not inner
automorphisms?

This was answered affirmatively by the formal reasoning agent Aristotle (Harmonic), as reported
in [vDJMM, Appendix A].
-/
@[category research solved, question, AMS 6 20,
  formal_proof using lean4 at
    "https://github.com/pitmonticone/Kourovka/blob/dcfdbdad8c434e30f6151fb3b4343364d70eeed4/Kourovka/Problem_21_149.lean#L770-L775",
  formal_proof using lean4 at
    "https://github.com/KitaKen1/kourovka-21-149-lean/blob/5c34c22661071d412f66a42009a1fe68db473b31/lean/Kourovka21149FC.lean#L5777-L5786"]
theorem kourovka_21_149.variants.not_inner :
    ∃ (K : Subgroup NNRealˣ) (G : Subgroup (ℝ ≃o ℝ)), IsDlabGroup K G ∧
      ∃ α : G ≃* G, (∀ f g : G, DlabLt (α f) (α g) ↔ DlabLt f g) ∧
        ¬ ∃ u : G, ∀ f : G, α f = u⁻¹ * f * u := by
  sorry

end Kourovka.«21.149»
