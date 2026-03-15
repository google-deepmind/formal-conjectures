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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 110

*Reference:* [erdosproblems.com/110](https://www.erdosproblems.com/110)

Is there a function $F$ such that every graph with chromatic number $\aleph_1$ has, for all
large $n$, a subgraph with chromatic number $n$ on at most $F(n)$ vertices? Disproved:
Lambie-Hanson constructed a ZFC counterexample.

[dBEr51] de Bruijn, N. G. and Erdős, P., _A colour problem for infinite graphs and a problem in
the theory of relations_. Indag. Math. (1951), 369–373.

[EHS82] Erdős, P., Hajnal, A., and Szemerédi, E., _On almost bipartite large chromatic graphs_.
Theory and Practice of Combinatorics (1982), 117–123.

[Er95d] Erdős, P., _On some problems in combinatorial set theory_. Publ. Inst. Math. (Beograd)
(N.S.) (1995), 61–65.

[KoSh05] Komjáth, P. and Shelah, S., _Finite subgraphs of uncountably chromatic graphs_.
J. Graph Theory (2005), 28–38.

[La20] Lambie-Hanson, C., _On the growth rate of chromatic numbers of finite subgraphs_.
Advances in Mathematics (2020), 107176.
-/

open SimpleGraph Cardinal

namespace Erdos110

/--
Erdős-Hajnal-Szemerédi Conjecture (Problem #110):
Is there some function $F : \mathbb{N} \to \mathbb{N}$ such that every graph $G$ with chromatic
number $\aleph_1$ has, for all sufficiently large $n$, a subgraph with chromatic number $n$ on at
most $F(n)$ vertices?

Conjectured by Erdős, Hajnal, and Szemerédi [EHS82].
The analogous statement fails for graphs of chromatic number $\aleph_0$.
Shelah [KoSh05] proved it is consistent with ZFC that the answer is no.
Lambie-Hanson [La20] constructed a ZFC counterexample, so the conjecture is **false**.
-/
@[category research solved, AMS 3 5]
theorem erdos_110 : answer(False) ↔
    ∃ F : ℕ → ℕ,
      ∀ (V : Type*) (G : SimpleGraph V),
        G.chromaticCardinal = aleph 1 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∃ H : G.Subgraph,
            H.verts.Finite ∧
            H.verts.ncard ≤ F n ∧
            H.coe.chromaticNumber = ↑n := by
  sorry

end Erdos110
