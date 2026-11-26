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
# Erdős Problem 1129

*References:*
- [erdosproblems.com/1129](https://www.erdosproblems.com/1129)
- [Be31] Bernstein, S., *Sur la limitation des valeurs d'un polynôme P_n(x) de degré n sur
  tout un segment par ses valeurs en (n+1) points du segment*. Izv. Akad. Nauk SSSR 7 (1931),
  1025-1050.
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
- [Fa14] Faber, G., *Über die interpolatorische Darstellung stetiger Funktionen*. Jahresber.
  Deutsch. Math.-Verein. 23 (1914), 190-210.
- [Ib16] Ibrahimoglu, B. A., *Lebesgue functions and Lebesgue constants in polynomial
  interpolation*. J. Inequal. Appl. (2016), Paper No. 93.
  [DOI](https://doi.org/10.1186/s13660-016-1030-3)
- [Ki77] Kilgore, T. A., *Optimization of the norm of the Lagrange interpolation operator*.
  Bull. Amer. Math. Soc. 83 (1977), 1069-1071.
- [Ki78] Kilgore, T. A., *A characterization of the Lagrange interpolating projection with
  minimal Tchebycheff norm*. J. Approx. Theory 24 (1978), 273-288.
- [RaVa15] Rack, H.-J. and Vajda, R., *Optimal cubic Lagrange interpolation: Extremal node
  systems with minimal Lebesgue constant*. Stud. Univ. Babeş-Bolyai Math. 60 (2015), 151-171.
  [Link](https://studia.reviste.ubbcluj.ro/index.php/subbmathematica/article/view/5710)
- [Ren26] Ren, C. Y., *Erdős 1129: all optimal free interpolation nodes*, Lean formalisation
  (2026), building on randyxian08's Lean formalisation of the canonical case.
  [GitHub](https://github.com/CollinYuanjieRen/awards/blob/791bf61df4366b60b6b47b9e062661ee65b3143b/submissions/jsp-000936-cyr/README.md)

See also [erdosproblems.com/1130](https://www.erdosproblems.com/1130), which uses the
definitions of this file.
-/

@[expose] public section

namespace Erdos1129

/-- A node set: $n$ points $-1\le x_1<\dots<x_n\le 1$, written as a strictly increasing map
`Fin n → ℝ` with values in $[-1,1]$. Distinct nodes are needed for the fundamental functions
$l_k$ to be defined (otherwise a division by zero gives a junk value). Ordering the nodes is no
restriction, because everything below is symmetric in the nodes. -/
def IsNodeSet {n : ℕ} (x : Fin n → ℝ) : Prop :=
  StrictMono x ∧ ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1

/-- The Lebesgue function $L_x(t)=\sum_k\lvert l_k(t)\rvert$ of the nodes `x`, where
$l_k(t)=\prod_{i\ne k}\frac{t-x_i}{x_k-x_i}$ is the Lagrange basis polynomial `Lagrange.basis`
(see `lebesgueFunction_eq` for the explicit product). -/
noncomputable def lebesgueFunction {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ k, |(Lagrange.basis Finset.univ x k).eval t|

/-- The explicit product formula for the Lebesgue function. -/
@[category API, AMS 41]
theorem lebesgueFunction_eq {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    lebesgueFunction x t = ∑ k, |∏ i ∈ Finset.univ.erase k, (t - x i) / (x k - x i)| := by
  simp only [lebesgueFunction, Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [div_eq_inv_mul]

/-- The Lebesgue constant $\Lambda(x)=\max_{t\in[-1,1]}L_x(t)$ of the nodes `x`. For a node set,
$L_x$ is continuous, so the supremum is attained. -/
noncomputable def lebesgueConstant {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup (lebesgueFunction x '' Set.Icc (-1 : ℝ) 1)

/-- The nodes together with the endpoints: `extendedNodes x 0` is $x_0=-1$, `extendedNodes x i` is
the node $x_i$ for $1\le i\le n$, and `extendedNodes x i` is $x_{n+1}=1$ for $i>n$. -/
noncomputable def extendedNodes {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ n then x ⟨i - 1, by omega⟩ else if i = 0 then -1 else 1

/-- `gapMax x i` is $\lambda_i(x)=\max_{t\in[x_i,x_{i+1}]}L_x(t)$ with $x_0=-1$ and $x_{n+1}=1$, for
$0\le i\le n$ (for larger `i` the value is not meaningful). For $1\le i\le n-1$ it is the local
maximum of the Lebesgue function between the consecutive nodes $x_i$ and $x_{i+1}$. If
$x_1=-1$ (respectively $x_n=1$) the gap $i=0$ (respectively $i=n$) is a single point, where
$L_x=1$. -/
noncomputable def gapMax {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  sSup (lebesgueFunction x '' Set.Icc (extendedNodes x i) (extendedNodes x (i + 1)))

/-- A canonical node set: a node set that contains both endpoints $x_1=-1$ and $x_n=1$. It exists
only for $n\ge 2$. -/
def IsCanonical {n : ℕ} (x : Fin n → ℝ) : Prop :=
  IsNodeSet x ∧ (-1 : ℝ) ∈ Set.range x ∧ (1 : ℝ) ∈ Set.range x

/-- `x` is a minimiser: a node set whose Lebesgue constant is at most that of every node set in
$[-1,1]$ with $n$ nodes. -/
def IsMinimiser {n : ℕ} (x : Fin n → ℝ) : Prop :=
  IsNodeSet x ∧ ∀ y : Fin n → ℝ, IsNodeSet y → lebesgueConstant x ≤ lebesgueConstant y

/-- Equioscillation: the $n-1$ local maxima $\lambda_1,\dots,\lambda_{n-1}$ of the Lebesgue
function between consecutive nodes are all equal. -/
def Equioscillates {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i ∈ Finset.Icc 1 (n - 1), ∀ j ∈ Finset.Icc 1 (n - 1), gapMax x i = gapMax x j

/-- `x` is the node set of the zeros of the Chebyshev polynomial $T_n$, in increasing order.
$T_n$ has $n$ simple zeros in $(-1,1)$, so there is exactly one such `x`. -/
def IsChebyshevNodes {n : ℕ} (x : Fin n → ℝ) : Prop :=
  IsNodeSet x ∧ ∀ j, (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (x j) = 0

/-- The answer: the node sets whose local maxima $\lambda_1,\ldots,\lambda_{n-1}$ between
consecutive nodes are all equal, and whose Lebesgue function at each endpoint $\pm 1$ is at most
$\lambda_1$, the common value (for $n\le 1$ the conditions hold for every node set). -/
def erdos_1129.answer (n : ℕ) : Set (Fin n → ℝ) :=
  {x | IsNodeSet x ∧ Equioscillates x ∧
    lebesgueFunction x (-1) ≤ gapMax x 1 ∧ lebesgueFunction x 1 ≤ gapMax x 1}

/--
For $x_1,\ldots,x_n\in [-1,1]$ let
$$l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)},$$
which are such that $l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$.

Describe which choice of $x_i$ minimise
$$\Lambda(x_1,\ldots,x_n)=\max_{x\in [-1,1]} \sum_k \lvert l_k(x)\rvert.$$

A problem of Bernstein [Be31] and Erdős [Er47, p. 1171], [Er67, p. 66]. They conjectured that
the minimisers are characterised by equioscillation of the Lebesgue function. This was proved by
Kilgore [Ki77], [Ki78] and by de Boor and Pinkus [dBPi78] for canonical node sets, that is, node
sets with $x_1=-1$ and $x_n=1$ (see [Ib16, Section 3.7] and [RaVa15, Proposition 2.8]); this is
`erdos_1129.variants.canonical`.

Here the minimisers range over all node sets in $[-1,1]$, as in the question. For $n\ge 3$ there
are uncountably many of them [RaVa15, Theorem 2.5] (`erdos_1129.variants.free_nodes_not_unique`):
suitable affine images of the canonical minimiser inside $[-1,1]$ are minimisers too. All of them
are described in the Lean formalisation [Ren26], which erdosproblems.com lists for this problem:
for $n\ge 2$ a node set minimises $\Lambda$ if and only if its local maxima between consecutive
nodes are all equal and both $\sum_k\lvert l_k(-1)\rvert$ and $\sum_k\lvert l_k(1)\rvert$ are at
most that common value, and for $n=1$ every node set minimises $\Lambda$. For $n=4$ all minimisers
are also given in [RaVa15, Theorem 5.2].
-/
@[category research solved, question value, AMS 41]
theorem erdos_1129 (n : ℕ) :
    {x : Fin n → ℝ | IsMinimiser x} = erdos_1129.answer n := by
  sorry

/--
The theorem of Kilgore [Ki77], [Ki78] and de Boor and Pinkus [dBPi78] for canonical node sets
($x_1=-1$, $x_n=1$), as in [Ib16, Section 3.7] and [RaVa15, Definition 2.7 and Proposition 2.8]:
the canonical node sets that minimise $\Lambda$ among all node sets are exactly the canonical node
sets whose local maxima $\lambda_i=\max_{[x_i,x_{i+1}]}\sum_k\lvert l_k\rvert$ between consecutive
nodes are all equal. The two outer gaps $[-1,x_1]$ and $[x_n,1]$ are single points for canonical
nodes and are not used.
-/
@[category research solved, AMS 41]
theorem erdos_1129.variants.canonical (n : ℕ) :
    {x : Fin n → ℝ | IsCanonical x ∧ IsMinimiser x} = {x | IsCanonical x ∧ Equioscillates x} := by
  sorry

/--
Kilgore [Ki78] and de Boor and Pinkus [dBPi78] proved that for $n\ge 2$ there is at most one
canonical node set whose local maxima $\lambda_1,\ldots,\lambda_{n-1}$ are all equal, and that it
is symmetric about $0$ ([Ib16, Section 3.7], [RaVa15, Proposition 2.8]). A canonical minimiser
exists ([RaVa15, Section 2]) and must equioscillate ([Ki77], [Ib16, Section 3.7]), so there is
exactly one such node set, and hence a unique canonical minimiser of $\Lambda$.
-/
@[category research solved, AMS 41]
theorem erdos_1129.variants.unique (n : ℕ) (hn : 2 ≤ n) :
    ∃! x : Fin n → ℝ, IsCanonical x ∧ Equioscillates x := by
  sorry

/--
Without the canonical hypothesis the minimiser of $\Lambda$ is not unique. For every $n\ge 3$
there are uncountably many node sets $x_1<\dots<x_n$ in $[-1,1]$ with the minimal Lebesgue
constant [RaVa15, Theorem 2.5]. The reason is affine invariance. Rescaling a node set to a
canonical one keeps its local maxima between consecutive nodes and does not increase $\Lambda$
([Ib16, Section 2.1 (e)]), so the minimal Lebesgue constant $\Lambda^*$ is attained by the
canonical minimiser $x^*$. The shrunk node set $x^*/\tau$ with $\tau\ge 1$ has
$\Lambda(x^*/\tau)=\max_{\lvert u\rvert\le\tau}L_{x^*}(u)$. Since $L_{x^*}(\pm 1)=1<\Lambda^*$ for
$n\ge 3$, this is still $\Lambda^*$ for all $\tau\ge 1$ close to $1$ (see the proof of
[RaVa15, Theorem 2.5]). For $n=4$ the node sets
$\pm 1/\tau,\pm t/\tau$ with $1\le\tau\le b$ for a constant $b\approx 1.0433$, where $t$ is as
in `erdos_1129.variants.four_nodes`, are all optimal [RaVa15, Theorem 4.2].
-/
@[category research solved, AMS 41]
theorem erdos_1129.variants.free_nodes_not_unique (n : ℕ) (hn : 3 ≤ n) :
    ¬ {x : Fin n → ℝ | IsMinimiser x}.Countable := by
  sorry

/--
For $n=3$ the canonical minimiser is $-1,0,1$, with $\Lambda=\frac54$ (Bernstein [Be31], see
[RaVa15, Section 2]).
-/
@[category research solved, AMS 41]
theorem erdos_1129.variants.three_nodes :
    {x : Fin 3 → ℝ | IsCanonical x ∧ IsMinimiser x} = ({![(-1 : ℝ), 0, 1]} : Set (Fin 3 → ℝ)) ∧
      lebesgueConstant (![(-1 : ℝ), 0, 1] : Fin 3 → ℝ) = 5 / 4 := by
  sorry

/--
For $n=4$ the canonical minimiser is $-1,-t,t,1$, where $t>0$ is the (unique positive) root of
$25t^6+17t^4+2t^2-1$, so $t\approx 0.4178$, and
$\Lambda=\frac{1+t^2}{1-t^2}\approx 1.4229$ [RaVa15, Section 3, (3.4)-(3.9)].
-/
@[category research solved, AMS 41]
theorem erdos_1129.variants.four_nodes (t : ℝ) (ht : 0 < t)
    (hroot : 25 * t ^ 6 + 17 * t ^ 4 + 2 * t ^ 2 - 1 = 0) :
    {x : Fin 4 → ℝ | IsCanonical x ∧ IsMinimiser x} =
        ({![(-1 : ℝ), -t, t, 1]} : Set (Fin 4 → ℝ)) ∧
      lebesgueConstant (![(-1 : ℝ), -t, t, 1] : Fin 4 → ℝ) = (1 + t ^ 2) / (1 - t ^ 2) := by
  sorry

/--
Faber [Fa14] proved $\Lambda(x_1,\ldots,x_n)\gg \log n$ for all choices of $x_i$, and Bernstein
[Be31] announced $\Lambda>(\frac{2}{\pi}-o(1))\log n$ (see [Er61c, p. 235]). Erdős [Er61c,
Theorem 1] improved this: there is an absolute constant $c_1$ such that for all
$-1\le x_1<\cdots<x_n\le 1$
$$\max_{x\in[-1,1]}\sum_k\lvert l_k(x)\rvert>\frac{2}{\pi}\log n-c_1.$$
-/
@[category research solved, AMS 41]
theorem erdos_1129.variants.erdos_lower_bound :
    ∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → ℝ), 1 ≤ n → IsNodeSet x →
      2 / Real.pi * Real.log n - C < lebesgueConstant x := by
  sorry

/--
This is best possible: for the zeros of the Chebyshev polynomial $T_n$ there is an absolute
constant $c_2$ with $\max_{x\in[-1,1]}\sum_k\lvert l_k(x)\rvert<\frac{2}{\pi}\log n+c_2$
([Er61c, p. 236], [Er67, p. 66]). [Ib16, Section 3.2] gives the precise asymptotics.
-/
@[category research solved, AMS 41]
theorem erdos_1129.variants.chebyshev_upper_bound :
    ∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → ℝ), 1 ≤ n → IsChebyshevNodes x →
      lebesgueConstant x < 2 / Real.pi * Real.log n + C := by
  sorry

end Erdos1129
