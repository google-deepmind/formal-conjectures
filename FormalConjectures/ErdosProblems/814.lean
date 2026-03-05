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
# Erdős Problem 814

*Reference:* [erdosproblems.com/814](https://www.erdosproblems.com/814)

Let $k \geq 2$ and $G$ be a graph with $n \geq k-1$ vertices and
$(k-1)(n-k+2) + \binom{k-2}{2} + 1$ edges. Does there exist some $c_k > 0$ such that $G$
must contain an induced subgraph on at most $(1-c_k)n$ vertices with minimum degree at least $k$?

The case $k=3$ was a problem of Erdős and Hajnal [Er91]. The question for general $k$ was a
conjecture of Erdős, Faudree, Rousseau, and Schelp [EFRS90], who proved that such a subgraph
exists with at most $n - c_k\sqrt{n}$ vertices. Mousset, Noever, and Skorić [MNS17] improved
this to $n - c_k \cdot n / \log n$. The full conjecture was proved by Sauermann [Sa19] with
$c_k \gg 1/k^3$.

[EFRS90] Erdős, P., Faudree, R., Rousseau, C., and Schelp, R.

[Er91] Erdős, P.

[MNS17] Mousset, F., Noever, A., and Skorić, N.

[Sa19] Sauermann, L.
-/

open SimpleGraph Finset

namespace Erdos814

/--
Erdős Problem 814 [EFRS90][Er91]:

For every $k \geq 2$, there exists $c > 0$ such that for all sufficiently large $n$,
every graph $G$ on $n$ vertices with at least $(k-1)(n-k+2) + \binom{k-2}{2} + 1$ edges
contains a nonempty vertex subset $S$ with $|S| \leq (1-c) \cdot n$ such that every vertex
in $S$ has at least $k$ neighbors within $S$.
-/
@[category research solved, AMS 5]
theorem erdos_814 :
    answer(True) ↔
    ∀ k : ℕ, k ≥ 2 →
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.edgeFinset.card ≥ (k - 1) * (n - k + 2) + (k - 2).choose 2 + 1 →
    ∃ S : Finset (Fin n),
      (S.card : ℝ) ≤ (1 - c) * (n : ℝ) ∧
      S.Nonempty ∧
      ∀ v ∈ S, k ≤ (S.filter (fun w => G.Adj v w)).card := by
  sorry

end Erdos814
