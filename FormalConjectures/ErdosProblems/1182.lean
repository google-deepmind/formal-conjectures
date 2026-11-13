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
# Erdős Problem 1182

*References:*
- [erdosproblems.com/1182](https://www.erdosproblems.com/1182)
- [Er78] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Proceedings of the Ninth Southeastern Conference on Combinatorics, Graph Theory, and
  Computing (Florida Atlantic Univ., Boca Raton, Fla., 1978) (1978), 29-40.
  [PDF](https://www.renyi.hu/~p_erdos/1978-36.pdf)
- [BEFRS80] Burr, S. A., Erdős, P., Faudree, R. J., Rousseau, C. C. and Schelp, R. H., *An extremal
  problem in generalized Ramsey theory*. Ars Combin. 10 (1980), 193-203.
  [PDF](https://www.renyi.hu/~p_erdos/1980-04.pdf)
- [Br96] Brandt, S., *Expanding graphs and Ramsey numbers*. Freie Universität Berlin, preprint
  A 96-24 (1996).
- [BBH98] Brandt, S., Brinkmann, G. and Harmuth, T., *All Ramsey numbers $r(K_3,G)$ for connected
  graphs of order 9*. Electron. J. Combin. 5 (1998), #R7.
- [Ch77] Chvátal, V., *Tree-complete graph Ramsey numbers*. J. Graph Theory 1 (1977), 93.
- [NiRo09] Nikiforov, V. and Rousseau, C. C., *Ramsey goodness and beyond*. Combinatorica 29
  (2009), 227-262.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1182

/-- A graph `G` on `n` vertices is *$3$-good* (in the sense of [BEFRS80], where a connected graph
is called $m$-good if $R(K_m,G)=(m-1)(n-1)+1$, here with $m=3$) if $R(K_3,G)=2n-1$, where $K_3$ is
`(⊤ : SimpleGraph (Fin 3))`. For connected `G` one always has $R(K_3,G)\ge 2n-1$ (see
`erdos_1182.variants.ramsey_ge`), so this says that the Ramsey number attains its lower bound.

[Er78, p. 33] states the problem for arbitrary graphs $G(n;\ell)$ with $R(K_3,G)\le 2n-1$; for
connected graphs this is the same as `IsTriangleGood`, and we follow [BEFRS80] and the problem
page in restricting to connected graphs. We only apply `IsTriangleGood` to connected graphs, which
have a vertex, so the natural-number subtraction is harmless. -/
def IsTriangleGood {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) G = 2 * n - 1

/-- $f(n)$: the largest number of edges of a connected $3$-good graph on $n$ vertices (this is
$g(n)$ in [BEFRS80]). A graph on $n$ vertices has at most $\binom n2$ edges and a path is
$3$-good (`erdos_1182.variants.chvatal`), so for $n\ge1$ the set is nonempty and bounded and
`sSup` is a genuine maximum. For $n=0$ there is no connected graph and `f 0 = 0`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {q : ℕ | ∃ G : SimpleGraph (Fin n), G.Connected ∧ G.edgeSet.ncard = q ∧ IsTriangleGood G}

/-- $F(n)$: the largest $q\le\binom n2$ such that every connected graph on $n$ vertices with at
most $q$ edges is $3$-good (this is $f(n)$ in [BEFRS80]). The set below is downward closed, so
`sSup` is its maximum; for $n\ge3$ it equals one less than the least number of edges of a
connected graph on $n$ vertices that is not $3$-good.

The condition $q\le\binom n2$ is only needed for $n\le2$, where every connected graph is
$3$-good: it gives `F 2 = 1`, as in the table of [BEFRS80], and `F 0 = F 1 = 0`. For $n\ge3$ it is
automatic, because the connected graph $K_n$ is not $3$-good (the complement of the odd cycle
$C_{2n-1}$ shows $R(K_3,K_n)>2n-1$). -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {q : ℕ | q ≤ n.choose 2 ∧
    ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard ≤ q → IsTriangleGood G}

/-- If `q ≤ n.choose 2` and every connected graph on `n` vertices with at most `q` edges is
$3$-good, then `q ≤ F n`. -/
@[category API, AMS 5]
theorem le_F {n q : ℕ} (hq : q ≤ n.choose 2)
    (h : ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard ≤ q → IsTriangleGood G) :
    q ≤ F n := by
  unfold F
  refine le_csSup ⟨n.choose 2, ?_⟩ ⟨hq, h⟩
  rintro p ⟨hp, -⟩
  exact hp

def erdos_1182.parts.i.answer : ℕ → ℝ := sorry

/--
Let $f(n)$ be maximal such that there is a connected graph $G$ with $n$ vertices and $f(n)$ edges
such that
$$R(K_3,G)= 2n-1.$$
Let $F(n)$ be maximal such that every connected graph $G$ with $n$ vertices and $\leq F(n)$ edges
has
$$R(K_3,G)= 2n-1.$$
Estimate $f(n)$ and $F(n)$. In particular, is it true that $F(n)/n\to \infty$?

This is the first part: estimate $f(n)$. The problem is due to Burr, Erdős, Faudree, Rousseau and
Schelp [BEFRS80] and appears in [Er78, p. 33]. We read "estimate" as the order of magnitude
`=Θ`. Burr, Erdős, Faudree, Rousseau and Schelp [BEFRS80, Theorem 2] proved
$n^{3/2}(\log n)^{1/2}\ll f(n)\ll n^{5/3}(\log n)^{2/3}$ (`erdos_1182.variants.f_lower`,
`erdos_1182.variants.f_upper`).
-/
@[category research open, question value, AMS 5]
theorem erdos_1182.parts.i :
    (fun n : ℕ ↦ (f n : ℝ)) =Θ[atTop] erdos_1182.parts.i.answer := by
  sorry

def erdos_1182.parts.ii.answer : ℕ → ℝ := fun n ↦ (n : ℝ)

/--
Let $f(n)$ be maximal such that there is a connected graph $G$ with $n$ vertices and $f(n)$ edges
such that
$$R(K_3,G)= 2n-1.$$
Let $F(n)$ be maximal such that every connected graph $G$ with $n$ vertices and $\leq F(n)$ edges
has
$$R(K_3,G)= 2n-1.$$
Estimate $f(n)$ and $F(n)$. In particular, is it true that $F(n)/n\to \infty$?

This is the second part: estimate $F(n)$. As an order of magnitude, `=Θ`, this is known:
$F(n)=\Theta(n)$, by $F(n)\ge n-1$ (`erdos_1182.variants.F_ge_pred`, from Chvátal's theorem
[Ch77]) and the linear upper bounds of `erdos_1182.variants.brandt` and
`erdos_1182.variants.nikiforov_rousseau`. The finer question of the asymptotic behaviour of
$F(n)/n$ is open, see `erdos_1182.variants.brandt_expects`.
-/
@[category research solved, question value, AMS 5]
theorem erdos_1182.parts.ii :
    (fun n : ℕ ↦ (F n : ℝ)) =Θ[atTop] erdos_1182.parts.ii.answer := by
  sorry

/--
Let $f(n)$ be maximal such that there is a connected graph $G$ with $n$ vertices and $f(n)$ edges
such that
$$R(K_3,G)= 2n-1.$$
Let $F(n)$ be maximal such that every connected graph $G$ with $n$ vertices and $\leq F(n)$ edges
has
$$R(K_3,G)= 2n-1.$$
Estimate $f(n)$ and $F(n)$. In particular, is it true that $F(n)/n\to \infty$?

This is the third part, asked in [BEFRS80, Section 5] and in [Er78, pp. 33-34], where Erdős says
it seems certain. The answer is no: Brandt [Br96] proved $F(n)\le 84n$ (as recorded on the problem
page, see `erdos_1182.variants.brandt`), and [NiRo09, Theorem 5.1] implies $F(n)<50n$ for large
$n$ (see `erdos_1182.variants.nikiforov_rousseau`).
-/
@[category research solved, question, AMS 5]
theorem erdos_1182.parts.iii :
    ¬ Tendsto (fun n : ℕ ↦ (F n : ℝ) / n) atTop atTop := by
  sorry

/--
It is trivial that $R(K_3,G)\geq 2n-1$ for any connected graph $G$ on $n$ vertices
([BEFRS80, p. 193]).
-/
@[category textbook, AMS 5]
theorem erdos_1182.variants.ramsey_ge {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    2 * n - 1 ≤ SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) G := by
  sorry

/--
By a result of Chvátal [Ch77], $R(K_3,T)=2n-1$ whenever $T$ is a tree on $n$ vertices (as stated
in [BEFRS80, p. 193]).
-/
@[category research solved, AMS 5]
theorem erdos_1182.variants.chvatal {n : ℕ} (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    IsTriangleGood T := by
  sorry

/--
Every connected graph with at most $n-1$ edges is a tree, so Chvátal's theorem [Ch77] gives
$F(n)\geq n-1$ ([BEFRS80, p. 193]).
-/
@[category research solved, AMS 5]
theorem erdos_1182.variants.F_ge_pred {n : ℕ} (hn : 2 ≤ n) : n - 1 ≤ F n := by
  sorry

/--
Burr, Erdős, Faudree, Rousseau and Schelp [BEFRS80, Theorem 1(a)] proved
$$\frac{17n+1}{15}\leq F(n),$$
the lower bound for all $n\geq 4$.

We state the integer-part version $n+\lfloor (2n+1)/15\rfloor\le F(n)$, which is what the proof
gives (the number $k$ of extra edges there is an integer with $0\le k\le (2n+1)/15$) and which
follows from the printed bound because $n+\lfloor (2n+1)/15\rfloor\leq(17n+1)/15$.
-/
@[category research solved, AMS 5]
theorem erdos_1182.variants.befrs_lower {n : ℕ} (hn : 4 ≤ n) :
    n + (2 * n + 1) / 15 ≤ F n := by
  sorry

/--
Burr, Erdős, Faudree, Rousseau and Schelp [BEFRS80, Theorem 1(b)] proved
$$F(n)\leq \left(\frac{27}{4}+o(1)\right)n(\log n)^2.$$
This is superseded by the linear bounds of `erdos_1182.variants.brandt` and
`erdos_1182.variants.nikiforov_rousseau`.
-/
@[category research solved, AMS 5]
theorem erdos_1182.variants.befrs_upper :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (F n : ℝ) < (27 / 4 + ε) * n * Real.log n ^ 2 := by
  sorry

/--
The upper bound was improved to $F(n)\leq 84n$ by Brandt [Br96]. (This resolves the final
question in the negative.)

We have not seen the preprint [Br96]; the bound is as recorded on the problem page, and we state
it for all large $n$. Brandt's method uses expander graphs: almost all regular graphs of large
degree are not $3$-good. In [BBH98, p. 6], of which Brandt is a coauthor, it is stated without
proof that it gives $F(n)<12n$ for large $n$ (there $F(n)$ is called $f(K_3,n)$).
-/
@[category research solved, AMS 5]
theorem erdos_1182.variants.brandt :
    ∀ᶠ n : ℕ in atTop, F n ≤ 84 * n := by
  sorry

/--
Nikiforov and Rousseau [NiRo09, Theorem 5.1] proved that for $n$ sufficiently large almost all
connected $100$-regular graphs of order $n$ are not $3$-good. Such a graph has $50n$ edges (and
connected $100$-regular graphs of order $n$ exist for all $n\geq 101$), so $F(n)<50n$ for all
large $n$. This gives a proved linear upper bound for $F$, answering the third part.
-/
@[category research solved, AMS 5]
theorem erdos_1182.variants.nikiforov_rousseau :
    ∀ᶠ n : ℕ in atTop, F n < 50 * n := by
  sorry

/--
Brandt [Br96] expects that for all large $n$ we have $2n<F(n)<6n$ (as recorded on the problem
page).
-/
@[category research open, AMS 5]
theorem erdos_1182.variants.brandt_expects :
    ∀ᶠ n : ℕ in atTop, 2 * n < F n ∧ F n < 6 * n := by
  sorry

/--
Burr, Erdős, Faudree, Rousseau and Schelp [BEFRS80, Theorem 2] proved that there is a constant
$A>0$ with
$$n^{3/2}(\log n)^{1/2} \ll f(n),$$
more precisely $An^{3/2}(\log n)^{1/2}<f(n)$ for all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_1182.variants.f_lower :
    ∃ A > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      A * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) < (f n : ℝ) := by
  sorry

/--
Burr, Erdős, Faudree, Rousseau and Schelp [BEFRS80, Theorem 2] proved that there is a constant
$B>0$ with
$$f(n)\ll n^{5/3}(\log n)^{2/3},$$
more precisely $f(n)<Bn^{5/3}(\log n)^{2/3}$ for all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_1182.variants.f_upper :
    ∃ B > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (f n : ℝ) < B * (n : ℝ) ^ (5 / 3 : ℝ) * Real.log n ^ (2 / 3 : ℝ) := by
  sorry

/--
The first few values of $F(n)$ and $f(n)$ (beginning with $n=2$) are $1,2,5,7,8$ and $1,2,5,8,12$
respectively, as reported in [BEFRS80, Table I]. Brandt, Brinkmann and Harmuth [BBH98, Table 2]
extended these (by computer) to all $n\le 12$:
$$F(n):\ 1,2,5,7,8,11,11,16,18,23,23,\qquad f(n):\ 1,2,5,8,12,16,20,27,33,41,49$$
for $n=2,\ldots,12$. (The value for $n=2$ is from [BEFRS80]; [BBH98] start at $n=3$.)
-/
@[category research solved, AMS 5]
theorem erdos_1182.variants.small_values :
    (F 2 = 1 ∧ F 3 = 2 ∧ F 4 = 5 ∧ F 5 = 7 ∧ F 6 = 8 ∧ F 7 = 11 ∧ F 8 = 11 ∧ F 9 = 16 ∧
      F 10 = 18 ∧ F 11 = 23 ∧ F 12 = 23) ∧
    (f 2 = 1 ∧ f 3 = 2 ∧ f 4 = 5 ∧ f 5 = 8 ∧ f 6 = 12 ∧ f 7 = 16 ∧ f 8 = 20 ∧ f 9 = 27 ∧
      f 10 = 33 ∧ f 11 = 41 ∧ f 12 = 49) := by
  sorry

end Erdos1182
