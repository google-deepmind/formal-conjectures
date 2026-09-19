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
# Erdős Problem 716

*References:*
- [erdosproblems.com/716](https://www.erdosproblems.com/716)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [BES73] Brown, W. G. and Erdős, P. and Sós, V. T., *Some extremal problems on $r$-graphs*.
  (1973), 53--63.
- [Er74c] Erdős, Paul, *Extremal problems on graphs and hypergraphs*. (1974), 75-84.
- [Er75] Erdős, P., *Some recent progress on extremal problems in graph theory*. Congr. Numer.
  (1975), 3-14.
- [Er75b] Erdős, Paul, *Problems and results in combinatorial number theory*. Journées
  Arithmétiques de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295-310.
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
- [RuSz78] Ruzsa, I. Z. and Szemerédi, E., *Triple systems with no six points carrying three
  triangles*. Combinatorics (Proc. Fifth Hungarian Colloq., Keszthely, 1976), Vol. II (1978),
  939-945.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos716

/-- The extremal number $\mathrm{ex}_3(n,\mathcal{F})$, where $\mathcal{F}$ is the family of all
$3$-uniform hypergraphs with $6$ vertices and $3$ edges: the maximum number of edges of a
$3$-uniform hypergraph on $n$ vertices in which no three distinct edges span at most six
vertices. -/
noncomputable def ex3 (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : Hypergraph (Fin n), H.vertexSet = Set.univ ∧
    (∀ e ∈ H.edgeSet, e.ncard = 3) ∧
    (¬ ∃ e₁ ∈ H.edgeSet, ∃ e₂ ∈ H.edgeSet, ∃ e₃ ∈ H.edgeSet,
      e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧ (e₁ ∪ e₂ ∪ e₃).ncard ≤ 6) ∧
    H.edgeSet.ncard = m}

/--
Let $\mathcal{F}$ be the family of all $3$-uniform hypergraphs with $6$ vertices and $3$
$3$-edges. Is it true that
$$\mathrm{ex}_3(n,\mathcal{F})=o(n^2)?$$

A conjecture of Brown, Erdős, and Sós [BES73]. The answer is yes, proved by Ruzsa and Szemerédi
[RuSz78] (this is known as the Ruzsa-Szemerédi problem).

See [1178](https://www.erdosproblems.com/1178) for the generalisation to $k$ vertices and $k-3$
edges, and [1157](https://www.erdosproblems.com/1157) for the completely general case.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos716.lean#L20"]
theorem erdos_716 : answer(True) ↔
    (fun n : ℕ => (ex3 n : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ 2 := by
  sorry

end Erdos716
