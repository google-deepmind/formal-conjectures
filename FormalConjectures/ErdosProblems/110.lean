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

public import FormalConjectures.ErdosProblems.«737»
public import FormalConjecturesUtil

/-!
# Erdős Problem 110

*References:*
- [erdosproblems.com/110](https://www.erdosproblems.com/110)
- [EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E., *On almost bipartite large chromatic graphs*.
  Theory and practice of combinatorics (1982), 117-123.
  [PDF](https://www.renyi.hu/~p_erdos/1982-11.pdf)
- [Er87] Erdős, P., *Some problems on finite and infinite graphs*. Logic and combinatorics
  (Arcata, Calif., 1985) (1987), 223-228. [PDF](https://www.renyi.hu/~p_erdos/1987-28.pdf)
- [Er95d] Erdős, Paul, *On some problems in combinatorial set theory*. Publ. Inst. Math.
  (Beograd) (N.S.) (1995), 61-65.
- [KoSh05] Komjáth, Péter and Shelah, Saharon, *Finite subgraphs of uncountably chromatic graphs*.
  J. Graph Theory (2005), 28--38.
- [La20] Lambie-Hanson, Chris, *On the growth rate of chromatic numbers of finite subgraphs*.
  Adv. Math. (2020), 107176, 13. [arXiv:1902.08177](https://arxiv.org/abs/1902.08177)
- [dBEr51] de Bruijn, N. G. and Erdős, P., *A colour problem for infinite graphs and a problem in
  the theory of relations*. Indag. Math. (1951), 369--373.
-/

@[expose] public section

open Filter

namespace Erdos110

set_option linter.style.formal_proof_palomar false in
/--
Is there some $F(n)$ such that every graph with chromatic number $\aleph_1$ has, for all large
$n$, a subgraph with chromatic number $n$ on at most $F(n)$ vertices?

A question of Erdős, Hajnal, and Szemerédi (see [EHS82], [Er87, p. 225, Problem 6], [Er95d]).
The answer is no: Komjáth and Shelah [KoSh05] proved that it is consistent that the answer is no,
and Lambie-Hanson [La20, Theorem A] constructed a counterexample in ZFC. The statement below is
therefore the negation. Subgraphs need not be induced, and finiteness of `H.verts` is explicit
because `Set.ncard` is `0` on infinite sets. Graphs are taken in `Type 1`, the universe of the
vertex type in the linked proof's construction. A counterexample in `Type` would give one in
`Type 1` by `ULift`; conversely, Lambie-Hanson's graph has $2^{\aleph_1}$ vertices, so it also
exists in `Type`.
-/
@[category research solved, question, AMS 3 5, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos110.lean#L161"]
theorem erdos_110 :
    ¬ ∃ F : ℕ → ℕ, ∀ (V : Type 1) (G : SimpleGraph V), Erdos737.ChromaticNumberAlephOne G →
      ∀ᶠ n : ℕ in atTop, ∃ H : G.Subgraph,
        H.verts.Finite ∧ H.verts.ncard ≤ F n ∧ H.coe.chromaticNumber = (n : ℕ∞) := by
  sorry

/--
Lambie-Hanson's quantitative theorem [La20, Theorem A], of which `erdos_110` is a consequence:
for every $f : \mathbb{N} \to \mathbb{N}$ there is a graph with chromatic number $\aleph_1$ such
that, for every $k \geq 3$, every finite subgraph with fewer than $f(k)$ vertices has chromatic
number less than $k$. (The graph constructed in [La20] has $2^{\aleph_1}$ vertices.)
-/
@[category research solved, AMS 3 5]
theorem erdos_110.variants.lambie_hanson (f : ℕ → ℕ) :
    ∃ (V : Type 1) (G : SimpleGraph V), Erdos737.ChromaticNumberAlephOne G ∧
      ∀ k : ℕ, 3 ≤ k → ∀ H : G.Subgraph, H.verts.Finite → H.verts.ncard < f k →
        H.coe.chromaticNumber < (k : ℕ∞) := by
  sorry

/--
A theorem of de Bruijn and Erdős [dBEr51] implies that, if $G$ has infinite chromatic number,
then $G$ has a finite subgraph of chromatic number $n$ for every $n\geq 1$.

Infinite chromatic number is `G.chromaticNumber = ⊤`.
-/
@[category research solved, AMS 5]
theorem erdos_110.variants.de_bruijn_erdos {V : Type*} (G : SimpleGraph V)
    (hG : G.chromaticNumber = ⊤) (n : ℕ) (hn : 1 ≤ n) :
    ∃ H : G.Subgraph, H.verts.Finite ∧ H.coe.chromaticNumber = (n : ℕ∞) := by
  sorry

end Erdos110
