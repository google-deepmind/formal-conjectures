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

import FormalConjecturesUtil

/-!
# The Bombieri–Lang conjecture

The Bombieri–Lang conjecture predicts that if $X$ is a smooth projective variety of general
type over a number field $K$, then the set $X(K)$ of $K$-rational points of $X$ is not Zariski
dense in $X$. For curves this is the Mordell conjecture, proved by Faltings. It is open in
every dimension $\geq 2$.

Mathlib does not yet have canonical bundles or Iitaka dimensions. We therefore state the
conjecture for the varieties of general type that can be described most concretely: smooth
hypersurfaces $X = V(f) \subseteq \mathbb{P}^n_K$ of degree $d$. The canonical bundle of such
an $X$ is $\mathcal{O}_X(d - n - 1)$, which is ample exactly when $d \geq n + 2$, so these are
exactly the smooth hypersurfaces of general type.

Everything is phrased in terms of homogeneous polynomials in $n + 1$ variables:

* a $K$-point of $\mathbb{P}^n$ is a nonzero vector $x \in K^{n+1}$, taken up to scaling; all
  the conditions below are invariant under scaling, see `BombieriLang.Points`;
* smoothness of $V(f)$ is the Jacobian criterion over $\overline{K}$, see
  `BombieriLang.IsSmooth`;
* Zariski density of $V(f)(K)$ in $V(f)$ says that a homogeneous polynomial vanishing at every
  $K$-point of $V(f)$ vanishes on all of $V(f)$. For $n \geq 2$ smoothness forces $f$ to be
  irreducible, so this says that it is divisible by $f$, see `BombieriLang.PointsDense`.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Bombieri%E2%80%93Lang_conjecture)
- [Lang1986] Serge Lang. Hyperbolic and Diophantine analysis,
  Bull. Amer. Math. Soc. 14 (1986), 159-205,
  https://www.ams.org/journals/bull/1986-14-02/S0273-0979-1986-15426-1/
- [Faltings1983] Gerd Faltings. Endlichkeitssätze für abelsche Varietäten über Zahlkörpern,
  Invent. Math. 73 (1983), 349-366, https://doi.org/10.1007/BF01388432
- [Poonen2017] Bjorn Poonen. Rational points on varieties, Graduate Studies in Mathematics 186,
  American Mathematical Society, 2017, https://math.mit.edu/~poonen/papers/Qpoints.pdf
-/

namespace BombieriLang

open MvPolynomial

variable {n : ℕ} {K : Type*} [Field K] [NumberField K]

/-- The set of $K$-rational points of the projective hypersurface $V(f) \subseteq \mathbb{P}^n_K$
cut out by a homogeneous polynomial `f` in $n + 1$ variables, described as the set of nonzero
vectors $x \in K^{n+1}$ with $f(x) = 0$. Two such vectors give the same point of
$\mathbb{P}^n_K$ exactly when they differ by a scalar. -/
def Points (f : MvPolynomial (Fin (n + 1)) K) : Set (Fin (n + 1) → K) :=
  {x | x ≠ 0 ∧ eval x f = 0}

/-- The hypersurface $V(f) \subseteq \mathbb{P}^n_K$ is smooth, expressed via the Jacobian
criterion over an algebraic closure $\overline{K}$: at every nonzero $\overline{K}$-point of
$V(f)$ some partial derivative of `f` is nonzero.

This excludes `f = 0`, since all partial derivatives of `0` vanish and $\overline{K}^{n+1}$
contains a nonzero vector. It also forces `f` to be squarefree, and irreducible once
$n \geq 2$. -/
def IsSmooth (f : MvPolynomial (Fin (n + 1)) K) : Prop :=
  ∀ x : Fin (n + 1) → AlgebraicClosure K, x ≠ 0 →
    eval x (f.map (algebraMap K (AlgebraicClosure K))) = 0 →
    ∃ i, eval x (pderiv i (f.map (algebraMap K (AlgebraicClosure K)))) ≠ 0

/-- The $K$-rational points of $V(f) \subseteq \mathbb{P}^n_K$ are Zariski dense in $V(f)$:
every homogeneous polynomial vanishing at all $K$-points of $V(f)$ vanishes on all of $V(f)$.
For `f` smooth with $n \geq 2$ the homogeneous ideal of $V(f)$ is `(f)`, so this says that `f`
divides it.

If $V(f)$ has no $K$-point at all, the hypothesis on `g` is vacuous, so `PointsDense f` forces
`f ∣ 1`. That fails for `f` homogeneous of positive degree, so `PointsDense f` is then false,
as it should be. -/
def PointsDense (f : MvPolynomial (Fin (n + 1)) K) : Prop :=
  ∀ g : MvPolynomial (Fin (n + 1)) K, (∃ e, g.IsHomogeneous e) →
    (∀ x ∈ Points f, eval x g = 0) → f ∣ g

/-- **The Bombieri–Lang conjecture** (for hypersurfaces). If $X = V(f) \subseteq \mathbb{P}^n_K$
is a smooth hypersurface of degree $d \geq n + 2$ over a number field $K$, then $X$ is of
general type, and the conjecture predicts that $X(K)$ is not Zariski dense in $X$.

See [Lang1986], [Poonen2017] and the Wikipedia entry. We require $n \geq 3$, so that
$\dim X = n - 1 \geq 2$ and the statement is open; the smallest case is that of smooth surfaces
of degree $\geq 5$ in $\mathbb{P}^3$. The excluded case $n = 2$, where $X$ is a smooth plane
curve of genus $\geq 3$, is Faltings' theorem, stated as `bombieri_lang.variants.curves`. -/
@[category research open, AMS 11 14]
theorem bombieri_lang (hn : 3 ≤ n) (d : ℕ) (hd : n + 2 ≤ d)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d) (hsmooth : IsSmooth f) :
    ¬ PointsDense f := by
  sorry

/-- **Faltings' theorem** (the Mordell conjecture) settles the case of curves, that is $n = 2$:
a smooth plane curve $V(f) \subseteq \mathbb{P}^2_K$ of degree $d$ has genus
$\binom{d - 1}{2} = (d - 1)(d - 2)/2$, which is at least $2$ exactly when $d \geq 4$, so such a
curve has only finitely many $K$-rational points. Here finiteness is expressed by saying that
the $K$-points span finitely many lines through the origin, that is, finitely many points of
$\mathbb{P}^2_K$. See [Faltings1983]. -/
@[category research solved, AMS 11 14]
theorem bombieri_lang.variants.curves (d : ℕ) (hd : 4 ≤ d) (f : MvPolynomial (Fin 3) K)
    (hf : f.IsHomogeneous d) (hsmooth : IsSmooth f) :
    ((fun x : Fin 3 → K => Submodule.span K {x}) '' Points f).Finite := by
  sorry

/-- The conclusion of the Bombieri–Lang conjecture in the case of curves, that is $n = 2$: for a
smooth plane curve of degree $d \geq 4$ the $K$-rational points are not Zariski dense. This is a
consequence of `bombieri_lang.variants.curves`: the finitely many $K$-points lie on a product of
linear forms, which is not divisible by the irreducible `f` since $d \geq 4 > 1$. -/
@[category research solved, AMS 11 14]
theorem bombieri_lang.variants.curves_not_dense (d : ℕ) (hd : 4 ≤ d)
    (f : MvPolynomial (Fin 3) K) (hf : f.IsHomogeneous d) (hsmooth : IsSmooth f) :
    ¬ PointsDense f := by
  sorry

end BombieriLang
