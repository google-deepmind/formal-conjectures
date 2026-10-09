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
# Erdős Problem 993

*References:*
 * [erdosproblems.com/993](https://www.erdosproblems.com/993)
 * [AMSE87] Alavi, Y., Malde, P. J., Schwenk, A. J. and Erdős, P., _The vertex independence
   sequence of a graph is not constrained_. Congr. Numer. **58** (1987), 15–23.
 * [Re26] Reynolds, B., _Mean bounds, structural reductions, and exhaustive verification for
   tree independence polynomial unimodality_, manuscript (2026),
   [paper/main_v2.tex](https://github.com/BrettRey/erdos-problem-993/blob/32dbb5d6982147835d4d8f4860e8c2e94efe2f2d/paper/main_v2.tex).
 * [Sc81] Schwenk, A. J., _On unimodal sequences of graphical invariants_. J. Combin. Theory
   Ser. B **30** (1981), 247–250.
-/

@[expose] public section

namespace Erdos993

/-- `indepSeq G k` is the number of `k`-element independent sets of `G`, i.e. the `k`-th term
$i_k(G)$ of the independence sequence. -/
noncomputable def indepSeq {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card {s : Finset V // s.card = k ∧ G.IsIndepSet (s : Set V)}

/-- A sequence `a : ℕ → ℕ` is *unimodal* if it is nondecreasing up to some index `m` and
nonincreasing thereafter. -/
def UnimodalSeq (a : ℕ → ℕ) : Prop :=
  ∃ m, (∀ i, i < m → a i ≤ a (i + 1)) ∧ (∀ i, m ≤ i → a (i + 1) ≤ a i)

/--
The independent set sequence of any tree or forest is unimodal.

In other words, if $i_k(G)$ counts the number of independent sets of vertices of size $k$ in a
graph $G$, and $T$ is any tree or forest, then for some $m\geq 0$
$$i_{0}(T)\leq i_{1}(T)\leq\cdots\leq i_{m}(T)\geq i_{m+1}(T)\geq i_{m+2}(T)\geq\cdots.$$

Forests are the acyclic graphs (`SimpleGraph.IsAcyclic`), so this statement includes trees. The
tree case alone is `erdos_993.variants.tree`. [AMSE87, p. 21] notes that a convolution of
unimodal sequences need not be unimodal, so the forest case does not follow from the tree case
by convolution alone, and suggests that the two cases "need to be attacked separately".
-/
@[category research open, AMS 5]
theorem erdos_993 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsAcyclic → UnimodalSeq (indepSeq G) := by
  sorry

/--
The independent set sequence of any finite tree is unimodal. This is the tree case of
`erdos_993` ([AMSE87, Problem 3]).
-/
@[category research open, AMS 5]
theorem erdos_993.variants.tree : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsTree → UnimodalSeq (indepSeq G) := by
  sorry

/-- The independence sequence of the equal-arm spider $S(2^k)$, a centre with $k$ arms of
length $2$ ($2k + 1$ vertices): $c_t = 2^t\binom{k}{t} + \binom{k}{t-1}$, where
$\binom{k}{-1} = 0$. -/
def spiderSeq (k t : ℕ) : ℕ := (if t = 0 then 0 else k.choose (t - 1)) + 2 ^ t * k.choose t

/--
**Local tie-balance for the equal-arm spider.** Let $c_t$ (`spiderSeq k t`) be the independence
sequence of the equal-arm spider $S(2^k)$. If $r < k$ and $c_r \le c_{r+1}$, then
$$N_r = \sum_{t} (t - r)\, c_t\, c_r^{t}\, c_{r+1}^{k+1-t} \ge 0,$$
equivalently $\mu(\lambda_r) \ge r$ at $\lambda_r = c_r / c_{r+1}$. Here $I(x) = \sum_t c_t x^t$
and $\mu(\lambda) = \lambda I'(\lambda) / I(\lambda)$ is the mean size of an independent set of
$S(2^k)$ under the hard-core measure at fugacity $\lambda$.

Context [Re26, Remark "Tie-fugacity condition", L329–L343]: for a tree $T$ on $n$ vertices with
leftmost mode $m$ and tie fugacity $\lambda_m = i_{m-1}(T)/i_m(T)$, the inequality
$\mu_T(\lambda_m) \ge m - 1$, together with the mean bound $\mu_T(1) < n/3$ proved there for
trees on $n \ge 3$ vertices in which every vertex has at most one leaf neighbour, would give
$\operatorname{mode} \le \lfloor n/3 \rfloor + 1$ for those trees (Conjecture A of [Re26]).
That is a bound on the mode, not unimodality. The route in [Re26, L259–L298] from Conjecture A
toward unimodality also needs the Case B hub bound (verified there only for $n \le 22$) and an
injection, or Hall-condition, argument between consecutive levels, both of which remain open.
[Re26] proves the tie-fugacity inequality for $S(2^k)$ at the leftmost mode (with
$6 \le k \le 11$ checked by direct computation); the statement here holds at every rising tie
and is proved in closed form. Spiders are already known to have log-concave independence
sequences ([Re26, L106, L645]), so this gives no new unimodality result. It does not prove
Conjecture A, and `erdos_993` remains open.
-/
@[category research solved, AMS 5,
  formal_proof using formal_conjectures at
    "https://github.com/AlperTheKing/formal-conjectures/blob/e9cb4f3cae9f6f252e553b1874be38e32544b55b/FormalConjectures/ErdosProblems/993.lean#L1338-L1343"]
theorem erdos_993.variants.equal_spider_local_tie_balance (k r : ℕ) (hr : r < k)
    (hrise : spiderSeq k r ≤ spiderSeq k (r + 1)) :
    0 ≤ ∑ t ∈ Finset.range (k + 2),
      ((t : ℚ) - r) * spiderSeq k t * (spiderSeq k r : ℚ) ^ t *
        (spiderSeq k (r + 1) : ℚ) ^ (k + 1 - t) := by
  sorry

/-- The independence sequence of the one-leaf mixed spider $S(2^a, 1)$, a centre with $a$ arms
of length $2$ and one arm of length $1$ ($2a + 2$ vertices):
$c_t = 2^t\binom{a}{t} + (2^{t-1} + 1)\binom{a}{t-1}$, where $\binom{a}{-1} = 0$. -/
def mixedSpiderSeq (a t : ℕ) : ℕ :=
  2 ^ t * a.choose t + (if t = 0 then 0 else (2 ^ (t - 1) + 1) * a.choose (t - 1))

/--
**Local tie-balance for the one-leaf mixed spider.** Let $c_t$ (`mixedSpiderSeq a t`) be the
independence sequence of $S(2^a, 1)$. For every $r < a$, with no rising-tie hypothesis,
$$N_r = \sum_{t} (t - r)\, c_t\, c_r^{t}\, c_{r+1}^{a+1-t} \ge 0,$$
equivalently $\mu(\lambda_r) \ge r$ at $\lambda_r = c_r / c_{r+1}$, in the notation of
`erdos_993.variants.equal_spider_local_tie_balance`. [Re26, Proposition "Mixed-spider
tie-fugacity", L649–L687] proves the tie-fugacity inequality for $S(2^a, 1)$, $a \ge 3$, at the
leftmost mode $m$ (the case $r = m - 1$ here), by exact computation for $a \le 200$ and an
asymptotic argument beyond; the statement here holds at every $r < a$. It does not prove
Conjecture A of [Re26], and `erdos_993` remains open.
-/
@[category research solved, AMS 5,
  formal_proof using formal_conjectures at
    "https://github.com/AlperTheKing/formal-conjectures/blob/e9cb4f3cae9f6f252e553b1874be38e32544b55b/FormalConjectures/ErdosProblems/993.lean#L1346-L1350"]
theorem erdos_993.variants.mixed_spider_one_leaf_local_tie_balance (a r : ℕ) (hr : r < a) :
    0 ≤ ∑ t ∈ Finset.range (a + 2),
      ((t : ℚ) - r) * mixedSpiderSeq a t * (mixedSpiderSeq a r : ℚ) ^ t *
        (mixedSpiderSeq a (r + 1) : ℚ) ^ (a + 1 - t) := by
  sorry

end Erdos993
