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
# Erdős Problem 934

*References:*
- [erdosproblems.com/934](https://www.erdosproblems.com/934)
- [Er88] Erdős, P., *Problems and results in combinatorial analysis and graph theory*.
  Discrete Math. 72 (1988), 81-92.
- [BBPP83] Bermond, J.-C., Bond, J., Paoli, M. and Peyrat, C., *Graphs and interconnection
  networks: diameter and vulnerability*. Surveys in Combinatorics (Southampton, 1983), London Math.
  Soc. Lecture Note Ser. 82, Cambridge Univ. Press (1983), 1-30.
- [CGTT90] Chung, F. R. K., Gyárfás, A., Tuza, Z. and Trotter, W. T., *The maximum number of
  edges in $2K_2$-free graphs of bounded degree*. Discrete Math. 81 (1990), 129-135.
- [CCJK22] Cambie, S., Cames van Batenburg, W., de Joannis de Verclos, R. and Kang, R. J.,
  *Maximising line subgraphs of diameter at most $t$*. SIAM J. Discrete Math. 36 (2022),
  939-950. [arXiv:2103.11898](https://arxiv.org/abs/2103.11898)
- [KMP26] Kumar, H., Mohar, B. and Pragada, S., *An improved bound for the strong clique index
  of graphs*. [arXiv:2607.02698](https://arxiv.org/abs/2607.02698) (2026).
- [CvBK26] Cames van Batenburg, W. and Korsky, S., *Asymptotically attaining the Moore bound*.
  [arXiv:2608.03965](https://arxiv.org/abs/2608.03965) (2026).
-/

@[expose] public section

open Filter

namespace Erdos934

/-- The graph `G` has two edges at distance at least `t`: there are edges `uv` and `wx` of `G`
such that every vertex of `{u, v}` is at graph distance at least `t` from every vertex of
`{w, x}`, i.e. the shortest path between the two edges has length at least `t`. We use the
extended distance `SimpleGraph.edist`, so vertices in different components are at distance `⊤`.
For `1 ≤ t` the two edges are automatically distinct (indeed vertex-disjoint): `t = 1` means
vertex-disjoint edges and `t = 2` means an induced `2K₂`. Only `1 ≤ t` is intended. -/
def HasFarEdges {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ u v w x : V, G.Adj u v ∧ G.Adj w x ∧
    ∀ a ∈ ({u, v} : Set V), ∀ b ∈ ({w, x} : Set V), (t : ℕ∞) ≤ G.edist a b

/-- `h t d` is $h_t(d)$: the least `m` such that every graph with at least `m` edges and maximum
degree at most `d` contains two edges at distance at least `t`. As in [CCJK22] and [KMP26],
"at least `m` edges" is used, so `h t d - 1` is the largest number of edges of a graph with
maximum degree at most `d` in which any two edges are at distance less than `t`, i.e. whose line
graph has diameter at most `t`. Graphs on `Fin n` for arbitrary `n` cover all finite graphs. The
set is nonempty (for example `3 * d ^ t / 2 + 1` belongs to it by [CCJK22, Theorem 6]), so
`sInf` is a genuine minimum. -/
noncomputable def h (t d : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ v, (G.neighborSet v).ncard ≤ d) → m ≤ G.edgeSet.ncard → HasFarEdges G t}

/-- If every graph with at least `m` edges and maximum degree at most `d` has two edges at
distance at least `t`, then `h t d ≤ m`. -/
@[category API, AMS 5]
theorem h_le {t d m : ℕ}
    (hm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ v, (G.neighborSet v).ncard ≤ d) → m ≤ G.edgeSet.ncard → HasFarEdges G t) :
    h t d ≤ m := by
  unfold h
  exact Nat.sInf_le hm

def erdos_934.answer : ℕ → ℕ → ℕ := sorry

/--
Let $h_t(d)$ be minimal such that every graph $G$ with $h_t(d)$ edges and maximal degree
$\leq d$ contains two edges whose shortest path between them has length $\geq t$.

Estimate $h_t(d)$.

A problem of Erdős and Nešetřil [Er88]. Erdős wrote 'This problem seems to be interesting only
if there is a nice expression for $h_t(d)$.' We read "estimate" as asking for an exact
expression, as in that remark: `h t d = erdos_934.answer t d` for all `1 ≤ t` and all `d`.
-/
@[category research open, question value, AMS 5]
theorem erdos_934 : ∀ t d : ℕ, 1 ≤ t → h t d = erdos_934.answer t d := by
  sorry

/--
It is easy to see that $h_t(d)\leq 2d^t$ always and $h_1(d)=d+1$.

The site (and [CCJK22, p. 1]) states $h_1(d)=d+1$ without restriction; it fails for $d=2$ (the
triangle has three pairwise intersecting edges, so $h_1(2)=4$), hence we assume $d\neq 2$.
-/
@[category research solved, AMS 5]
theorem erdos_934.variants.h_one : ∀ d : ℕ, d ≠ 2 → h 1 d = d + 1 := by
  sorry

/--
Erdős and Nešetřil and Bermond, Bond, Paoli, and Peyrat [BBPP83] independently conjectured that
$h_2(d) \leq \tfrac{5}{4}d^2+1$, with equality for even $d$. This was proved by Chung, Gyárfás,
Tuza, and Trotter [CGTT90].
-/
@[category research solved, AMS 5]
theorem erdos_934.variants.h_two :
    (∀ d : ℕ, 4 * h 2 d ≤ 5 * d ^ 2 + 4) ∧
      ∀ d : ℕ, Even d → 4 * h 2 d = 5 * d ^ 2 + 4 := by
  sorry

/--
Cambie, Cames van Batenburg, de Joannis de Verclos, and Kang [CCJK22, Theorem 2] proved that $h_3(3)=23$.
-/
@[category research solved, AMS 5]
theorem erdos_934.variants.h_three_three : h 3 3 = 23 := by
  sorry

/--
The same authors prove that for all $t\geq 1$ we have
$$h_t(d) \leq \tfrac{3}{2}d^t+1.$$
See [CCJK22, Theorem 6]. Here the inequality is stated as `2 * h t d ≤ 3 * d ^ t + 2`.
-/
@[category research solved, AMS 5]
theorem erdos_934.variants.upper :
    ∀ t d : ℕ, 1 ≤ t → 2 * h t d ≤ 3 * d ^ t + 2 := by
  sorry

/--
The same authors prove that, if $t$ is large, then there are infinitely many $d$ such that
$h_t(d) \geq 0.629^td^t$. See [CCJK22, Proposition 5].
-/
@[category research solved, AMS 5]
theorem erdos_934.variants.lower_large_t :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      ∃ᶠ d : ℕ in atTop, ((629 : ℝ) / 1000) ^ t * (d : ℝ) ^ t ≤ (h t d : ℝ) := by
  sorry

/--
Cambie, Cames van Batenburg, de Joannis de Verclos, and Kang [CCJK22] conjectured that
$h_3(d) \leq d^3-d^2+d+2$ (with equality if $d-1$ is a prime power; the site writes "if and only
if", while [CCJK22, Conjecture 1] says "if"). Kumar, Mohar and Pragada [KMP26, Lemma 3.1]
refute the inequality: the odd graph $KG(7,3)$ has $35$ vertices, is $4$-regular, has $70$ edges
and any two of its edges are at distance less than $3$, so $h_3(4)\geq 71 > 54$.
-/
@[category research solved, AMS 5]
theorem erdos_934.variants.kmp_h_three_four : 71 ≤ h 3 4 := by
  sorry

/--
The inequality $h_3(d) \leq d^3-d^2+d+2$ conjectured in [CCJK22] is false [KMP26, Conjecture 1.9
and Lemma 3.1]. Here the inequality is stated as `h 3 d + d ^ 2 ≤ d ^ 3 + d + 2`.
-/
@[category research solved, AMS 5]
theorem erdos_934.variants.ccjk_conjecture_false :
    ¬ ∀ d : ℕ, h 3 d + d ^ 2 ≤ d ^ 3 + d + 2 := by
  sorry

/--
Kumar, Mohar and Pragada [KMP26, Theorem 1.11] proved
$$\liminf_{d\to\infty}\frac{h_3(d)}{d^3}\geq \frac{253}{225}.$$
In particular the conjecture of [CCJK22] that $h_t(d)\leq (1+o(1))d^t$ is false for $t=3$.
-/
@[category research solved, AMS 5]
theorem erdos_934.variants.kmp_liminf :
    ∀ ε > (0 : ℝ), ∀ᶠ d : ℕ in atTop, (253 / 225 - ε) * (d : ℝ) ^ 3 ≤ (h 3 d : ℝ) := by
  sorry

/--
For every fixed $t\geq 2$, $\liminf_{d\to\infty} h_t(d)/d^t \geq 1$ [CvBK26, Corollary 1.2]. This
confirms, in a strong form, the conjecture of [CCJK22] that $h_t(d)\geq (1-o(1))d^t$ for
infinitely many $d$.
-/
@[category research solved, AMS 5]
theorem erdos_934.variants.lower_liminf :
    ∀ t : ℕ, 2 ≤ t → ∀ ε > (0 : ℝ), ∀ᶠ d : ℕ in atTop,
      (1 - ε) * (d : ℝ) ^ t ≤ (h t d : ℝ) := by
  sorry

end Erdos934
