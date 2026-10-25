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
# Erdős Problem 59

*References:*
- [erdosproblems.com/59](https://www.erdosproblems.com/59)
- [EFR86] Erdős, P., Frankl, P. and Rödl, V., *The asymptotic number of graphs not containing a
  fixed subgraph and a problem for hypergraphs having no exponent*. Graphs Combin. (1986),
  113-121.
- [MoSa16] Morris, R. and Saxton, D., *The number of $C_{2\ell}$-free graphs*. Adv. Math. (2016),
  534-580. [arXiv:1309.2927](https://arxiv.org/abs/1309.2927)
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999 (1999).
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos59

/-- `numFree H n` is the number of labelled graphs on the vertex set `Fin n` which do not
contain `H` as a subgraph. -/
noncomputable def numFree {k : ℕ} (H : SimpleGraph (Fin k)) (n : ℕ) : ℕ :=
  {G : SimpleGraph (Fin n) | H.Free G}.ncard

/-- If `H` has an edge, the empty graph on `Fin n` is `H`-free, so `numFree H n` is positive. -/
@[category API, AMS 5]
theorem numFree_pos {k : ℕ} {H : SimpleGraph (Fin k)} (hH : H ≠ ⊥) (n : ℕ) :
    0 < numFree H n := by
  unfold numFree
  exact (Set.ncard_pos (Set.toFinite _)).2 ⟨⊥, SimpleGraph.free_bot hH⟩

/--
Is it true that the number of graphs on $n$ vertices which do not contain $G$ is
$$\leq 2^{(1+o(1))\mathrm{ex}(n;G)}?$$

The answer is no, already for $G=C_6$ (see `erdos_59.variants.morris_saxton`). Graphs are
labelled, and $G$ ranges over finite graphs containing a cycle, as in [MoSa16]; for some forests
the answer is trivially no (for the path with two edges the free graphs include all matchings,
about $2^{\Theta(n\log n)}$ of them).
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos59.lean#L46"]
theorem erdos_59 :
    ¬ ∀ (k : ℕ) (H : SimpleGraph (Fin k)), ¬ H.IsAcyclic →
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        (numFree H n : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * (extremalNumber n H : ℝ)) := by
  sorry

/--
If $G$ is not bipartite the answer is yes, proved by Erdős, Frankl, and Rödl [EFR86].
-/
@[category research solved, AMS 5]
theorem erdos_59.variants.erdos_frankl_rodl {k : ℕ} (H : SimpleGraph (Fin k))
    (hH : ¬ H.IsBipartite) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (numFree H n : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * (extremalNumber n H : ℝ)) := by
  sorry

/--
The answer is no for $G=C_6$, the cycle on 6 vertices. Morris and Saxton [MoSa16, Proposition
1.4] have proved there are at least
$$2^{(1+c)\mathrm{ex}(n;C_6)}$$
such graphs for infinitely many $n$, for some constant $c>0$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos59.lean#L46"]
theorem erdos_59.variants.morris_saxton :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ ((1 + c) * (extremalNumber n (cycleGraph 6) : ℝ)) ≤
        (numFree (cycleGraph 6) n : ℝ) := by
  sorry

/--
In [Va99] the specific case of $G=C_4$ is also asked.
-/
@[category research open, question, AMS 5]
theorem erdos_59.variants.c4 :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (numFree (cycleGraph 4) n : ℝ) ≤
        (2 : ℝ) ^ ((1 + ε) * (extremalNumber n (cycleGraph 4) : ℝ)) := by
  sorry

/--
It is still possible (and conjectured by Morris and Saxton) that the weaker bound of
$$2^{O(\mathrm{ex}(n;G))}$$
holds for all $G$ containing a cycle.
-/
@[category research open, AMS 5]
theorem erdos_59.variants.big_o :
    ∀ (k : ℕ) (H : SimpleGraph (Fin k)), ¬ H.IsAcyclic →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
        (numFree H n : ℝ) ≤ (2 : ℝ) ^ (C * (extremalNumber n H : ℝ)) := by
  sorry

end Erdos59
