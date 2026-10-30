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
public import FormalConjectures.ErdosProblems.«1047»

/-!
# Erdős Problem 1042

*References:*
- [erdosproblems.com/1042](https://www.erdosproblems.com/1042)
- [EHP58] Erdős, P. and Herzog, F. and Piranian, G., *Metric properties of polynomials*.
  J. Analyse Math. (1958), 125-148. [PDF](https://www.renyi.hu/~p_erdos/1958-05.pdf)
- [GhRa24] Ghosh, S. and Ramachandran, K., *Number of components of polynomial lemniscates: a
  problem of Erdős, Herzog, and Piranian*. J. Math. Anal. Appl. (2024), Paper No. 128571.
  [arXiv:2312.13673](https://arxiv.org/abs/2312.13673)
-/

@[expose] public section

open Filter Polynomial Erdos1047
open scoped ENNReal

namespace Erdos1042

/-- The $n$-th diameter of $F\subseteq\mathbb{C}$:
$$\sup_{z_1,\ldots,z_n\in F}\Bigl(\prod_{i<j}\lvert z_i-z_j\rvert\Bigr)^{1/\binom{n}{2}}.$$
The points need not be distinct. The value lies in `ℝ≥0∞`, so it is $\infty$ (and not a junk
value $0$) when $F$ is unbounded and $n\ge 2$. For $n<2$ the exponent is $0$; these values are
irrelevant for the limit below. -/
noncomputable def nthDiameter (F : Set ℂ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ z : Fin n → ℂ, ⨆ _ : ∀ i, z i ∈ F,
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, edist (z i) (z j)) ^ (1 / ((n.choose 2 : ℕ) : ℝ))

/-- The transfinite diameter of $F\subseteq\mathbb{C}$ (also called the logarithmic capacity, by
the Fekete--Szegő theorem), defined as in the problem as the limit of the $n$-th diameters.
The $n$-th diameters are non-increasing in $n\ge 2$ (Fekete), so the limit exists in `ℝ≥0∞` and
`limsup` is that limit. It is $\infty$ for unbounded $F$, so a closed set of finite transfinite
diameter is compact. -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ≥0∞ :=
  Filter.limsup (fun n : ℕ ↦ nthDiameter F n) atTop

/-- `f` is a monic polynomial of degree `n` all of whose roots lie in `F`, that is,
$f(z)=\prod_{i=1}^n(z-z_i)$ with all $z_i\in F$. -/
def MonicWithRootsIn (F : Set ℂ) (n : ℕ) (f : ℂ[X]) : Prop :=
  f.Monic ∧ f.natDegree = n ∧ ∀ z ∈ f.roots, z ∈ F

/-- The number of connected components of the open set $\{ z: \lvert f(z)\rvert < 1\}$.
For non-constant `f` each component contains a root of `f` (maximum modulus principle), so there
are at most `deg f` components and `Set.ncard` is the true count. For `f = 1` the set is
empty. -/
noncomputable def numComponents (f : ℂ[X]) : ℕ :=
  (componentsIn (strictSublevelSet f 1)).ncard

/--
Let $F\subset\mathbb{C}$ be a closed set of transfinite diameter $1$ which is not contained in
any closed disc of radius $1$.

If $f(z)=\prod_{i=1}^n(z-z_i)\in\mathbb{C}[x]$ with all $z_i\in F$ then can
$$\{ z: \lvert f(z)\rvert < 1\}$$
have $n$ connected components?

A problem of Erdős, Herzog, and Piranian [EHP58, p. 139, Problem 6], who proved that if $F$ is the
disc of radius $1$ then this set can have $n$ connected components (for example $f(z)=z^n+1$).

As in the answer of Ghosh and Ramachandran [GhRa24] to their Question 1.2, we read "can"
existentially: there is such an $F$ for which $n$ components occur for infinitely many $n$.
[GhRa24] answer this question in the affirmative; the classical example $F=[-2,2]$
[GhRa24, Example 2.7] already gives $n$ components for every $n\ge 1$, see
`erdos_1042.variants.chebyshev_segment`. The universal reading, for every such $F$, is
`erdos_1042.variants.universal`.
-/
@[category research solved, question, AMS 30]
theorem erdos_1042.parts.i :
    ∃ F : Set ℂ, IsClosed F ∧ transfiniteDiameter F = 1 ∧
      (∀ c : ℂ, ¬ F ⊆ Metric.closedBall c 1) ∧
      ∃ᶠ n : ℕ in atTop, ∃ f : ℂ[X], MonicWithRootsIn F n f ∧ numComponents f = n := by
  sorry

/--
Ghosh and Ramachandran [GhRa24, Example 2.7] note that for $F=[-2,2]\subset\mathbb{C}$ (a closed
set of transfinite diameter $1$ which is not contained in any closed disc of radius $1$) the
monic Chebyshev polynomial $f_n(z)=2T_n(z/2)$ has all its roots in $F$ and all its $n-1$ critical
values equal to $\pm 2$, so $\{\lvert f_n\rvert<1\}$ has exactly $n$ components, for every
$n\ge 1$.
-/
@[category research solved, AMS 30]
theorem erdos_1042.variants.chebyshev_segment (F : Set ℂ)
    (hF : F = Complex.ofReal '' Set.Icc (-2 : ℝ) 2) :
    IsClosed F ∧ transfiniteDiameter F = 1 ∧ (∀ c : ℂ, ¬ F ⊆ Metric.closedBall c 1) ∧
      ∀ n : ℕ, 1 ≤ n → ∃ f : ℂ[X], MonicWithRootsIn F n f ∧ numComponents f = n := by
  sorry

/--
The first question of [EHP58, p. 139, Problem 6] read universally: for every closed $F$ of
transfinite diameter $1$ which is not contained in any closed disc of radius $1$, are there
infinitely many $n$ for which some $f$ with all roots in $F$ gives $n$ components?

This is not settled by [GhRa24], who prove it for closed lemniscates [GhRa24, Proposition 2.3]
and conjecture the weaker statement $\limsup_n C_n(F)/n=1$ for every compact $F$ of capacity $1$
[GhRa24, §2.1.1]. "Some $n$" instead of infinitely many would be trivial ($n=1$).
-/
@[category research open, question, AMS 30]
theorem erdos_1042.variants.universal :
    ∀ F : Set ℂ, IsClosed F → transfiniteDiameter F = 1 →
      (∀ c : ℂ, ¬ F ⊆ Metric.closedBall c 1) →
      ∃ᶠ n : ℕ in atTop, ∃ f : ℂ[X], MonicWithRootsIn F n f ∧ numComponents f = n := by
  sorry

/--
If the transfinite diameter of $F$ is $<1$ then must this set only have at most $(1-c)n$
connected components, where $c>0$ depends only on $F$ (or just the transfinite diameter of $F$)?

This is the second question of [EHP58, p. 139, Problem 6], which asks for $n$ large. It was solved
by Ghosh and Ramachandran [GhRa24, Theorem 2.1(a)], who proved that, if $d$ is the transfinite
diameter of $F$ and $0<d<1$, then the set has at most $(1-c)n$ connected components for some
$c>0$ depending on $F$. Precisely, they prove $\limsup_n C_n(F)/n<1$, where $C_n(F)$ is the
maximal number of components over all admissible $f$ of degree $n$; this is the statement below.
The answer is yes, in this form.

[GhRa24] assume throughout that $F$ is compact of positive capacity, so we assume $0<d$; a closed
$F$ with $d<1$ is bounded, hence compact. The condition "$n$ large" is needed: for $n=1$ the set
$\{\lvert z-z_1\rvert<1\}$ has one component, which is more than $(1-c)n$. The parenthetical
"or just the transfinite diameter of $F$" is not formalised: [GhRa24] only remark that their
quantities $M(K)$ and $m(K)$ are not determined by the capacity.
-/
@[category research solved, question, AMS 30]
theorem erdos_1042.parts.ii :
    ∀ F : Set ℂ, IsClosed F → 0 < transfiniteDiameter F → transfiniteDiameter F < 1 →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ f : ℂ[X], MonicWithRootsIn F n f →
        (numComponents f : ℝ) ≤ (1 - c) * n := by
  sorry

/--
If $d\leq 1/4$ and $F$ is connected then the set has only one connected component.

This is [GhRa24, Theorem 2.1(c)]: if the logarithmic capacity of the compact connected set $K$ is
at most $1/4$ then $\{\lvert f\rvert<1\}$ is connected for every monic $f$ with all roots in $K$.
We take the degree $n\ge 1$ (for $n=0$ the set is empty) and, as in [GhRa24], positive capacity.
-/
@[category research solved, AMS 30]
theorem erdos_1042.variants.connected_le_quarter (F : Set ℂ) (hF : IsClosed F)
    (hconn : IsConnected F) (h₀ : 0 < transfiniteDiameter F) (hd : transfiniteDiameter F ≤ 1 / 4)
    (n : ℕ) (hn : 1 ≤ n) (f : ℂ[X]) (hf : MonicWithRootsIn F n f) :
    numComponents f = 1 := by
  sorry

end Erdos1042
