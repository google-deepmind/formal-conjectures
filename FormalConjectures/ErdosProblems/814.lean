/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 814

*References:*
- [erdosproblems.com/814](https://www.erdosproblems.com/814)
- [EFRS90] Erdős, P. and Faudree, R. J. and Rousseau, C. C. and Schelp, R. H., _Subgraphs of
  minimal degree k_. Discrete Math. (1990), 53--58.
- [Er91] Erdős, P., _Problems and results in combinatorial analysis and combinatorial number
  theory_. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [Er93] Erdős, Paul, _Some of my favorite solved and unsolved problems in graph theory_.
  Quaestiones Math. (1993), 333-350.
- [MNS17] Mousset, Frank and Noever, Andreas and Škorić, Nemanja, _Smaller subgraphs of minimum
  degree k_. Electron. J. Combin. (2017), Paper No. 4.9, 8.
- [Sa19] Sauermann, Lisa, _A proof of a conjecture of Erdős, Faudree, Rousseau and Schelp on
  subgraphs of minimum degree k_. J. Combin. Theory Ser. B (2019), 36--75.
-/

@[expose] public section

open Filter Real SimpleGraph

namespace Erdos814

open scoped Classical in
/--
Let $k\geq 2$ and $G$ be a graph with $n\geq k-1$ vertices and
$$(k-1)(n-k+2)+\binom{k-2}{2}+1$$
edges. Does there exist some $c_k>0$ such that $G$ must contain an induced subgraph on at most
$(1-c_k)n$ vertices with minimum degree at least $k$?

The case $k=3$ was a problem of Erdős and Hajnal [Er91]. The question for general $k$ was a
conjecture of Erdős, Faudree, Rousseau, and Schelp [EFRS90], who proved that such a subgraph
exists with at most $n-c_k\sqrt{n}$ vertices. Mousset, Noever, and Skorić [MNS17] improved
this to $n-c_k\frac{n}{\log n}$. The full conjecture was proved by Sauermann [Sa19], who proved
this with $c_k \gg 1/k^3$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos814.lean#L81"]
theorem erdos_814 : answer(True) ↔
    ∀ k ≥ 2, ∃ c > 0, ∀ n ≥ k - 1, ∀ G : SimpleGraph (Fin n),
      G.edgeFinset.card = (k - 1) * (n + 2 - k) + (k - 2).choose 2 + 1 →
        ∃ S : Finset (Fin n), S.Nonempty ∧ (S.card : ℝ) ≤ (1 - c) * n ∧
          k ≤ (G.induce (S : Set (Fin n))).minDegree := by
  sorry

open scoped Classical in
/-- The conclusion holds as soon as $G$ has at least $(k-1)(n-k+2)+inom{k-2}{2}+1$ edges
(Sauermann [Sa19]). -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos814.lean#L59"]
theorem erdos_814.variants.at_least :
    ∀ k ≥ 2, ∃ c > 0, ∀ n ≥ k - 1, ∀ G : SimpleGraph (Fin n),
      (k - 1) * (n + 2 - k) + (k - 2).choose 2 + 1 ≤ G.edgeFinset.card →
        ∃ S : Finset (Fin n), S.Nonempty ∧ (S.card : ℝ) ≤ (1 - c) * n ∧
          k ≤ (G.induce (S : Set (Fin n))).minDegree := by
  sorry

open scoped Classical in
/-- Sauermann [Sa19] proved this with $c_k \gg 1/k^3$. -/
@[category research solved, AMS 5]
theorem erdos_814.variants.sauermann :
    ∃ C > 0, ∀ k ≥ 2, ∀ n ≥ k - 1, ∀ G : SimpleGraph (Fin n),
      (k - 1) * (n + 2 - k) + (k - 2).choose 2 + 1 ≤ G.edgeFinset.card →
        ∃ S : Finset (Fin n), S.Nonempty ∧ (S.card : ℝ) ≤ (1 - C / k ^ 3) * n ∧
          k ≤ (G.induce (S : Set (Fin n))).minDegree := by
  sorry

end Erdos814
