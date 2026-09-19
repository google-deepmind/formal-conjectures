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
# Erdős Problem 815

*References:*
- [erdosproblems.com/815](https://www.erdosproblems.com/815)
- [EFGS88] Erdős, P. and Faudree, R. and Gyárfás, A. and Schelp, R. H., *Cycles in graphs
  without proper subgraphs of minimum degree 3*. Ars Combin. (1988), 195-201.
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [NPS17] Narins, Lothar and Pokrovskiy, Alexey and Szabó, Tibor, *Graphs without proper
  subgraphs of minimum degree 3 and short cycles*. Combinatorica (2017), 495-519.
-/

@[expose] public section

open Filter SimpleGraph
open scoped SimpleGraph

namespace Erdos815

open scoped Classical in
/--
A graph on `n` vertices is *degree $3$ critical* if it has `2n - 2` edges and every proper
induced subgraph has minimum degree `≤ 2`.
-/
def IsDegreeThreeCritical {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.edgeFinset.card = 2 * n - 2 ∧
    ∀ s : Set (Fin n), s ≠ Set.univ → (G.induce s).minDegree ≤ 2

/--
Let $k\geq 3$ and $n$ be sufficiently large. Is it true that if $G$ is a graph with $n$ vertices
and $2n-2$ edges such that every proper induced subgraph has minimum degree $\leq 2$ then $G$
must contain a copy of $C_k$?

In [Er91] Erdős attributes this to himself and Hajnal, claiming they could prove it for
$3\leq k\leq 6$, but it appears in an earlier paper of Erdős, Faudree, Gyárfás, and Schelp
[EFGS88], where they prove that such a graph on $n\geq 5$ vertices contains cycles of length $3$,
$4$, and $5$, and a cycle of length at least $\lfloor \log_2n\rfloor$, and need not contain a
cycle of length longer than $\sqrt{n}$.

Such graphs are called degree $3$ critical. This conjecture was disproved by Narins, Pokrovskiy,
and Szabó [NPS17], who proved that there are arbitrarily large such graphs with no cycle of length
$23$. It remains open whether this question has an affirmative answer if we restrict to even $k$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos815.lean#L2075"]
theorem erdos_815 : answer(False) ↔ ∀ k : ℕ, 3 ≤ k → ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin n), IsDegreeThreeCritical G → cycleGraph k ⊑ G := by
  sorry

/--
Narins, Pokrovskiy, and Szabó [NPS17] proved that there are arbitrarily large degree $3$ critical
graphs with no cycle of length $23$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos815.lean#L1972"]
theorem erdos_815.variants.twenty_three : ∃ᶠ n : ℕ in atTop,
    ∃ G : SimpleGraph (Fin n), IsDegreeThreeCritical G ∧ ¬ cycleGraph 23 ⊑ G := by
  sorry

/-- It remains open whether this question has an affirmative answer if we restrict to even $k$. -/
@[category research open, AMS 5]
theorem erdos_815.variants.even : answer(sorry) ↔ ∀ k : ℕ, 3 ≤ k → Even k →
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), IsDegreeThreeCritical G → cycleGraph k ⊑ G := by
  sorry

/--
Erdős, Faudree, Gyárfás, and Schelp [EFGS88] proved that a degree $3$ critical graph on $n\geq 5$
vertices contains cycles of length $3$, $4$, and $5$.
-/
@[category research solved, AMS 5]
theorem erdos_815.variants.small_cycles : ∀ n : ℕ, 5 ≤ n →
    ∀ G : SimpleGraph (Fin n), IsDegreeThreeCritical G →
      cycleGraph 3 ⊑ G ∧ cycleGraph 4 ⊑ G ∧ cycleGraph 5 ⊑ G := by
  sorry

/--
Erdős, Faudree, Gyárfás, and Schelp [EFGS88] proved that a degree $3$ critical graph on $n\geq 5$
vertices contains a cycle of length at least $\lfloor \log_2n\rfloor$.
-/
@[category research solved, AMS 5]
theorem erdos_815.variants.long_cycle : ∀ n : ℕ, 5 ≤ n → ∀ G : SimpleGraph (Fin n),
    IsDegreeThreeCritical G → ∃ k : ℕ, Nat.log 2 n ≤ k ∧ cycleGraph k ⊑ G := by
  sorry

end Erdos815
