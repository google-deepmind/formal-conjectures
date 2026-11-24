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
# Ben Green's Open Problem 56

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.56)
- [GGMT25] W. T. Gowers, B. Green, F. Manners and T. Tao, *On a conjecture of Marton*.
  Ann. of Math. (2) 201 (2025), no. 2, 515-549. [arXiv:2311.05762](https://arxiv.org/abs/2311.05762)
- [GGMT24] W. T. Gowers, B. Green, F. Manners and T. Tao, *Marton's Conjecture in abelian groups
  with bounded torsion*. [arXiv:2404.02244](https://arxiv.org/abs/2404.02244) (2024).
- [GT10] B. Green and T. Tao, *An equivalence between inverse sumset theorems and inverse
  conjectures for the $U^3$ norm*. Math. Proc. Cambridge Philos. Soc. 149 (2010), no. 1, 1-19.
  [arXiv:0906.3100](https://arxiv.org/abs/0906.3100)
-/

@[expose] public section

namespace Green56

/--
`iterDeriv k h f` is the iterated multiplicative derivative
$\Delta_{h_1} \Delta_{h_2} \cdots \Delta_{h_k} f$ of $f : G \to \mathbb{C}$, where
$\Delta_h f(x) = f(x) \overline{f(x + h)}$ (`multiplicativeDerivative`) and `h : Fin k → G`.
The derivatives commute, so the order of the steps is immaterial.
-/
noncomputable def iterDeriv {G : Type*} [AddCommGroup G] :
    (k : ℕ) → (Fin k → G) → (G → ℂ) → (G → ℂ)
  | 0, _, f => f
  | k + 1, h, f => multiplicativeDerivative (h 0) (iterDeriv k (Fin.tail h) f)

/--
`gowersNormPow k f` is $\lVert f \rVert_{U^k}^{2^k}$ for $f : G \to \mathbb{C}$ on a finite
abelian group $G$, namely
$\mathbb{E}_{x, h_1, \dots, h_k \in G} \Delta_{h_1} \cdots \Delta_{h_k} f(x)$
(the real part of this average, which is a non-negative real number). We work with the
$2^k$-th power so that no roots are needed: $\lVert f \rVert_{U^k} \ge \delta$ for
$\delta \ge 0$ is the same as `δ ^ 2 ^ k ≤ gowersNormPow k f`.
-/
noncomputable def gowersNormPow {G : Type*} [AddCommGroup G] [Fintype G] (k : ℕ) (f : G → ℂ) :
    ℝ :=
  (((Fintype.card G : ℂ) ^ (k + 1))⁻¹ * ∑ x : G, ∑ h : Fin k → G, iterDeriv k h f x).re

/--
`phaseCorrelation p n f ψ` is $\left|\mathbb{E}_{x \in \mathbb{F}_p^n} f(x) e(-\psi(x)/p)\right|$
for a polynomial $\psi \in \mathbb{F}_p[x_1, \dots, x_n]$ evaluated at $x$, where
$e(t/p) = \exp(2 \pi i t / p)$ (`ZMod.stdAddChar`).
-/
noncomputable def phaseCorrelation (p n : ℕ) [Fact p.Prime] (f : 𝔽 p n → ℂ)
    (ψ : MvPolynomial (Fin n) (ZMod p)) : ℝ :=
  ‖(1 / (p ^ n : ℂ)) * ∑ x : 𝔽 p n, f x * ZMod.stdAddChar (-(MvPolynomial.eval x ψ))‖

/--
**Polynomial Gowers Inverse Conjecture** [Gr24, Problem 56].

"Bounds for the inverse theorem for Gowers norms." Green's comments: "Over finite fields, the
question is simpler to state and it is natural to make the following 'Polynomial Gowers Inverse
Conjecture'. Fix an integer $s \geqslant 1$, and let $p > s$. Suppose that
$f : \mathbb{F}_p^n \to \mathbb{C}$ is a function with $|f(x)| \leqslant 1$ for all $x$, and that
$\lVert f \rVert_{U^{s+1}} \geqslant \delta$. Then there is a form $\psi$ of degree $s$ such that
$|\mathbb{E}_{x \in \mathbb{F}_p^n} f(x) e(-2\pi i \psi(x)/p)| \gg \delta^{O_s(1)}$."

Reading: the headline of the problem is only a topic, so the statement is the conjecture
quoted above. Here the exponent is a constant $C$ depending only on $s$, as the notation
$O_s(1)$ indicates. The place of the constant $c$ implied by $\gg$ is a separate formalisation
choice of ours. Read with the notation convention of [Gr24], where implied constants are absolute,
the display asks for an absolute $c$; we let $c$ depend on $s$ and $p$ (but not on $n$, $f$ or
$\delta$), which gives a weaker statement. A "form of degree $s$" is a polynomial of total degree
at most $s$ (its constant term is allowed). The hypothesis is the $2^{s+1}$-th power form
`δ ^ 2 ^ (s + 1) ≤ gowersNormPow (s + 1) f`, and $0 < \delta \le 1$ since the norm of a
$1$-bounded function is at most $1$. Green's $e(-2\pi i \psi(x)/p)$ is $e^{-2\pi i \psi(x)/p}$.

The statement is open as a whole. [Gr24] (update 2023) reports that "polynomially effective bounds
for the case $s = 2$ are now known"; the exponent in these bounds depends on $p$ (see
`green_56.variants.s_two_odd_char`), so they do not give the case $s = 2$ of this statement. In
the reading with $p$ fixed and an exponent that may depend on $p$, which the source also supports,
the case $s = 2$ is known and the open part is $s \ge 3$ (`green_56.variants.fixed_prime`).
-/
@[category research open, AMS 5 11 42]
theorem green_56 :
    ∀ s : ℕ, 1 ≤ s → ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ) [Fact p.Prime], s < p → ∃ c : ℝ, 0 < c ∧
        ∀ (n : ℕ) (f : 𝔽 p n → ℂ), (∀ x, ‖f x‖ ≤ 1) →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ^ 2 ^ (s + 1) ≤ gowersNormPow (s + 1) f →
            ∃ ψ : MvPolynomial (Fin n) (ZMod p), ψ.totalDegree ≤ s ∧
              c * δ ^ C ≤ phaseCorrelation p n f ψ := by
  sorry

/--
The Polynomial Gowers Inverse Conjecture for a fixed prime $p$, in which the exponent may also
depend on $p$, for $s \ge 3$ (for $s = 2$ this form is known, see below). It is weaker than
`green_56`, where the exponent depends on $s$ only.

This reading is supported by the source. For the equivalence of the case $s = 2$ with Marton's
conjecture, [Gr24] cites [GT10] (and, independently, Lovett), and the remark after Theorem 1.12 of
[GT10] says that "a similar result would hold over $\mathbb{F}_p$, for any fixed prime $p$, though
the exponents obtained would depend on $p$". The 2023 update of [Gr24] counts the bounds that
follow from [GGMT25] and [GGMT24] as polynomially effective bounds for the case $s = 2$; in
[GGMT24] the exponent is $O(p^3)$.

[Gr24, Problem 56] reports quantitative (but not polynomial) bounds for $s \ge 3$ from
Gowers–Milićević and quasipolynomial bounds for $s = 3$ from Milićević.
-/
@[category research open, AMS 5 11 42]
theorem green_56.variants.fixed_prime :
    ∀ s : ℕ, 3 ≤ s → ∀ (p : ℕ) [Fact p.Prime], s < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (n : ℕ) (f : 𝔽 p n → ℂ), (∀ x, ‖f x‖ ≤ 1) →
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ^ 2 ^ (s + 1) ≤ gowersNormPow (s + 1) f →
          ∃ ψ : MvPolynomial (Fin n) (ZMod p), ψ.totalDegree ≤ s ∧
            c * δ ^ C ≤ phaseCorrelation p n f ψ := by
  sorry

/--
The case $s = 2$ in odd characteristic [GGMT24, Corollary 1.2]: "Let $p$ be odd. Let
$f : \mathbb{F}_p^n \to \mathbb{C}$ be a $1$-bounded function, and suppose that
$\lVert f \rVert_{U^3(\mathbb{F}_p^n)} \geqslant \eta$ for some $\eta$,
$0 < \eta \leqslant \tfrac{1}{2}$. Then there is a quadratic polynomial
$\phi : \mathbb{F}_p^n \to \mathbb{F}_p$ such that
$|\mathbb{E}_{x \in \mathbb{F}_p^n} f(x) e_p(-\phi(x))| \gg \eta^{O(p^3)}$." In [GGMT24] the
constants implied by $\gg$ and $O$ are absolute, so the exponent is $A p^3$ for an absolute
constant $A$.
-/
@[category research solved, AMS 5 11 42]
theorem green_56.variants.s_two_odd_char :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (n : ℕ) (f : 𝔽 p n → ℂ), (∀ x, ‖f x‖ ≤ 1) →
        ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → η ^ 2 ^ 3 ≤ gowersNormPow 3 f →
          ∃ φ : MvPolynomial (Fin n) (ZMod p), φ.totalDegree ≤ 2 ∧
            c * η ^ (A * (p : ℝ) ^ 3) ≤ phaseCorrelation p n f φ := by
  sorry

/--
The case $s = 2$ in characteristic $2$ [GGMT25, Corollary 1.6]: there is a constant $C_5$
such that if $f : \mathbb{F}_2^n \to \mathbb{C}$ is $1$-bounded and
$\lVert f \rVert_{U^3} \ge 1/K$, then there is a quadratic polynomial
$P : \mathbb{F}_2^n \to \mathbb{F}_2$ with
$|\mathbb{E}_x f(x) (-1)^{P(x)}| \gg K^{-C_5}$. Here $\delta = 1/K \in (0, 1]$, and
`ZMod.stdAddChar` on `ZMod 2` is $t \mapsto (-1)^t$. The constants are absolute.
-/
@[category research solved, AMS 5 11 42]
theorem green_56.variants.s_two_char_two :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (n : ℕ) (f : 𝔽 2 n → ℂ), (∀ x, ‖f x‖ ≤ 1) →
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ^ 2 ^ 3 ≤ gowersNormPow 3 f →
          ∃ P : MvPolynomial (Fin n) (ZMod 2), P.totalDegree ≤ 2 ∧
            c * δ ^ C ≤ phaseCorrelation 2 n f P := by
  sorry

end Green56
