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
public import FormalConjectures.ErdosProblems.«1129»

/-!
# Erdős Problem 1130

*References:*
- [erdosproblems.com/1130](https://www.erdosproblems.com/1130)
- [dBPi78] de Boor, C. and Pinkus, A., *Proof of the conjectures of Bernstein and Erdős
  concerning the optimal nodes for polynomial interpolation*. J. Approx. Theory 24 (1978),
  289-303.
- [Er47] Erdős, P., *Some remarks on polynomials*. Bull. Amer. Math. Soc. 53 (1947), 1169-1176.
  [PDF](https://www.renyi.hu/~p_erdos/1947-08.pdf)
- [Er61c] Erdős, P., *Problems and results on the theory of interpolation. II*. Acta Math.
  Acad. Sci. Hungar. 12 (1961), 235-244. [PDF](https://www.renyi.hu/~p_erdos/1961-20.pdf)
- [Er67] Erdős, P., *Problems and results on the convergence and divergence properties of the
  Lagrange interpolation polynomials and some extremal problems*. Mathematica (Cluj) (1967),
  65-73. [PDF](https://www.renyi.hu/~p_erdos/1967-20.pdf)
- [Ib16] Ibrahimoglu, B. A., *Lebesgue functions and Lebesgue constants in polynomial
  interpolation*. J. Inequal. Appl. (2016), Paper No. 93.
  [DOI](https://doi.org/10.1186/s13660-016-1030-3)
- [Ki77] Kilgore, T. A., *Optimization of the norm of the Lagrange interpolation operator*.
  Bull. Amer. Math. Soc. 83 (1977), 1069-1071.
- [Ki78] Kilgore, T. A., *A characterization of the Lagrange interpolating projection with
  minimal Tchebycheff norm*. J. Approx. Theory 24 (1978), 273-288.

The definitions (nodes, Lebesgue function, canonical node sets, equioscillation) are in
`FormalConjectures.ErdosProblems.«1129»`, the file of
[erdosproblems.com/1129](https://www.erdosproblems.com/1129).
-/

@[expose] public section

open Erdos1129

namespace Erdos1130

/-- $\Upsilon(x)=\min_{0\le i\le n}\max_{t\in[x_i,x_{i+1}]}L_x(t)$ with $x_0=-1$ and $x_{n+1}=1$:
the smallest of the $n+1$ local maxima `gapMax x i`, $0\le i\le n$. If $x_1=-1$ or $x_n=1$ then an
outer gap is a single point, where the Lebesgue function is $1$, and $\Upsilon(x)=1$. -/
noncomputable def upsilon {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ⨅ i : Fin (n + 1), gapMax x (i : ℕ)

/-- The smallest of the $n-1$ local maxima $\lambda_1,\dots,\lambda_{n-1}$ of the Lebesgue function
between consecutive nodes. For a canonical node set this is the smallest local maximum of the
Lebesgue function (the quantity $m_n(X)$ of [Ib16, Section 2.1 (c)]). It is meaningful for
$n\ge 2$. -/
noncomputable def minInteriorGapMax {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ⨅ i : Fin (n - 1), gapMax x ((i : ℕ) + 1)

/--
For $x_1,\ldots,x_n\in [-1,1]$ let
$$l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)},$$
which are such that $l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$.

Let $x_0=-1$ and $x_{n+1}=1$ and
$$\Upsilon(x_1,\ldots,x_n)=\min_{0\leq i\leq n}\max_{x\in[x_i,x_{i+1}]}
\sum_k \lvert l_k(x)\rvert.$$
Is it true that
$$\Upsilon(x_1,\ldots,x_n)\ll \log n?$$

This is the first part, a question of Erdős [Er67, p. 66], who could prove only
$\Upsilon<\sqrt n$ [Er47, Theorem 2]. We read $\ll$ as: there is an absolute constant $C$ with
$\Upsilon(x_1,\ldots,x_n)\le C\log n$ for all $n\ge 2$ and all nodes
$-1\le x_1<\cdots<x_n\le 1$. The answer is yes: $\Upsilon(x)$ is at most the minimal Lebesgue
constant (`erdos_1130.variants.erdos_inequality`, from [Ki77], [Ki78] and [dBPi78]), and the
Chebyshev nodes show that this is $<\frac2\pi\log n+O(1)$ [Er61c, p. 236].
-/
@[category research solved, question, AMS 41]
theorem erdos_1130.parts.i :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x : Fin n → ℝ), 2 ≤ n → IsNodeSet x →
      upsilon x ≤ C * Real.log n := by
  sorry

/-- The set of all node sets that maximise $\Upsilon$. The cited sources describe the maximisers
only among canonical node sets, with $\Upsilon$ replaced (`erdos_1130.variants.canonical`), so it
is left as `sorry`. -/
def erdos_1130.parts.ii.answer (n : ℕ) : Set (Fin n → ℝ) := sorry

/--
For $x_1,\ldots,x_n\in [-1,1]$ let
$$l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)},$$
which are such that $l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$.

Let $x_0=-1$ and $x_{n+1}=1$ and
$$\Upsilon(x_1,\ldots,x_n)=\min_{0\leq i\leq n}\max_{x\in[x_i,x_{i+1}]}
\sum_k \lvert l_k(x)\rvert.$$
Describe which choice of $x_i$ maximise $\Upsilon(x_1,\ldots,x_n)$.

This is the second part. Erdős [Er47, p. 1172], [Er67, p. 66] conjectured that the maximisers are
the node sets of [erdosproblems.com/1129](https://www.erdosproblems.com/1129), characterised by
equal local maxima. This was proved by Kilgore [Ki77], [Ki78] and by de Boor and Pinkus [dBPi78]
for canonical node sets, with the smallest local maximum between consecutive nodes in place of
$\Upsilon$ (see [Ib16, Section 3.7]); this is `erdos_1130.variants.canonical`.

Here, as in the question, $\Upsilon$ includes the two outer gaps and the maximisers range over
all node sets in $[-1,1]$. A maximiser is then not unique in general, and it need not have all
$n+1$ local maxima $\lambda_0,\ldots,\lambda_n$ equal: for $n=3$ the nodes $-s,0,s$ with
$0<s\le\frac{2\sqrt2}{3}$ all give $\Upsilon=\frac54$, the largest possible value, and for
$s=\frac12$ the four local maxima are $7,\frac54,\frac54,7$. The cited sources do not describe the
whole set of maximisers, so `erdos_1130.parts.ii.answer` is left as `sorry`.
-/
@[category research solved, question value, AMS 41]
theorem erdos_1130.parts.ii (n : ℕ) :
    {x : Fin n → ℝ | IsNodeSet x ∧ ∀ y : Fin n → ℝ, IsNodeSet y → upsilon y ≤ upsilon x} =
      erdos_1130.parts.ii.answer n := by
  sorry

/--
The theorem of Kilgore [Ki77], [Ki78] and de Boor and Pinkus [dBPi78] in the form of
[Ib16, Section 3.7]: among canonical node sets ($x_1=-1$, $x_n=1$), the ones at which the smallest
of the $n-1$ local maxima between consecutive nodes is largest are exactly the canonical node sets
whose local maxima between consecutive nodes are all equal, that is, the canonical minimisers of
$\Lambda$ (`Erdos1129.erdos_1129.variants.canonical`). For canonical nodes the two outer gaps are
single points and the literal $\Upsilon$ is $1$, which is why $\Upsilon$ is replaced by
`minInteriorGapMax` here.
-/
@[category research solved, AMS 41]
theorem erdos_1130.variants.canonical (n : ℕ) :
    {x : Fin n → ℝ | IsCanonical x ∧
      ∀ y : Fin n → ℝ, IsCanonical y → minInteriorGapMax y ≤ minInteriorGapMax x} =
        {x | IsCanonical x ∧ Equioscillates x} := by
  sorry

/--
The inequality conjectured by Erdős and proved by Kilgore [Ki77], [Ki78] and by de Boor and
Pinkus [dBPi78] (stated in
[Ib16, Section 3.7] as $m_n(X)\le \Lambda_n(X^*)$ for every node set $X$): the smallest local
maximum of the Lebesgue function of any node set is at most the minimal Lebesgue constant. Here
$y$ is a minimiser of $\Lambda$. For nodes that contain neither $-1$ nor $1$, $\Upsilon$ is this
smallest local maximum [Ib16, Section 2.1 (b), (c)]; otherwise $\Upsilon=1$.
-/
@[category research solved, AMS 41]
theorem erdos_1130.variants.erdos_inequality (n : ℕ) (x y : Fin n → ℝ)
    (hx : IsNodeSet x) (hy : IsMinimiser y) :
    upsilon x ≤ lebesgueConstant y := by
  sorry

/--
The same inequality for a canonical node set `x`, in the form of [Ib16, Section 3.7]: the smallest
of the local maxima between consecutive nodes is at most the minimal Lebesgue constant.
-/
@[category research solved, AMS 41]
theorem erdos_1130.variants.erdos_inequality_canonical (n : ℕ) (x y : Fin n → ℝ)
    (hx : IsCanonical x) (hy : IsMinimiser y) :
    minInteriorGapMax x ≤ lebesgueConstant y := by
  sorry

/--
It follows from `erdos_1130.variants.erdos_inequality` and the bound for Chebyshev nodes in
[Er61c, p. 236] that
$$\Upsilon(x_1,\ldots,x_n)\le\frac{2}{\pi}\log n+O(1).$$
-/
@[category research solved, AMS 41]
theorem erdos_1130.variants.log_bound :
    ∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → ℝ), 1 ≤ n → IsNodeSet x →
      upsilon x ≤ 2 / Real.pi * Real.log n + C := by
  sorry

/--
Erdős [Er47, Theorem 2, pp. 1171-1172] proved that for nodes $x_1\le\cdots\le x_n$ in $[-1,1]$
there is an $i$ with $\max_{x\in[x_i,x_{i+1}]}\sum_k\lvert l_k(x)\rvert<\sqrt n$, that is,
$\Upsilon(x_1,\ldots,x_n)<\sqrt n$. The paper allows coinciding nodes (then it calls the claim
obvious); here the nodes are distinct. We take $n\ge 2$: for $n=1$ the sum is identically $1$.
-/
@[category research solved, AMS 41]
theorem erdos_1130.variants.erdos_sqrt (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : IsNodeSet x) :
    upsilon x < Real.sqrt n := by
  sorry

end Erdos1130
