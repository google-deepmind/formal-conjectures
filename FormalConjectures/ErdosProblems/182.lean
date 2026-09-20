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
# Erdős Problem 182

*References:*
- [erdosproblems.com/182](https://www.erdosproblems.com/182)
- [Er75] Erdős, P., *Some recent progress on extremal problems in graph theory*. Congr. Numer.
  (1975), 3-14.
- [Er78] Erdős, Paul, *Problems and results in combinatorial analysis and combinatorial number
  theory*. Proceedings of the Ninth Southeastern Conference on Combinatorics, Graph Theory, and
  Computing (Florida Atlantic Univ., Boca Raton, Fla., 1978) (1978), 29-40.
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
- [JaSu23] Janzer, Oliver and Sudakov, Benny, *Resolution of the Erdős-Sauer problem on regular
  subgraphs*. Forum Math. Pi (2023), Paper No. e19, 13.
- [CJMM24b] D. Chakraborti, O. Janzer, A. Methuku, and R. Montgomery, *Regular subgraphs at every
  density*. arXiv:2411.11785 (2024).
- [PRS95] Pyber, L. and Rödl, V. and Szemerédi, E., *Dense subgraphs without 3-regular
  subgraphs*. Journal of Combinatorial Theory, Series B (1995), 41-54.
-/

@[expose] public section

open Filter Asymptotics SimpleGraph

namespace Erdos182

/-- `G` contains a nonempty (not necessarily induced or spanning) `k`-regular subgraph. -/
def ContainsRegularSubgraph {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.verts.Finite ∧
    ∀ v : H.verts, (H.coe.neighborSet v).ncard = k

/--
`f n k` is the maximum number of edges of a graph on `n` vertices with no nonempty `k`-regular
subgraph.
-/
noncomputable def f (n k : ℕ) : ℕ :=
  sSup {m | ∃ G : SimpleGraph (Fin n), ¬ ContainsRegularSubgraph G k ∧ G.edgeSet.ncard = m}

/--
Let $k\geq 3$. What is the maximum number of edges that a graph on $n$ vertices can contain if it
does not have a $k$-regular subgraph? Is it $\ll n^{1+o(1)}$?

Asked by Erdős and Sauer. The prize of \$100 is offered in [Er78] for the case $k=3$ (perhaps
just for settling whether the answer is $\ll n$ or not). Resolved by Janzer and Sudakov [JaSu23],
who proved that there exists some $C=C(k)>0$ such that any graph on $n$ vertices with at least
$Cn\log\log n$ edges contains a $k$-regular subgraph.

Chakraborti, Janzer, Methuku, and Montgomery [CJMM24b] have shown that one can take
$C(k)\ll k^2$, which is the best possible up to an absolute constant.

A construction due to Pyber, Rödl, and Szemerédi [PRS95] shows that this is best possible.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos182.lean#L93"]
theorem erdos_182 : answer(True) ↔ ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, (f n k : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by
  sorry

/--
Janzer and Sudakov [JaSu23] and Pyber, Rödl, and Szemerédi [PRS95]: for fixed $k\geq 3$ the
extremal number has order exactly $n\log\log n$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos182.lean#L74"]
theorem erdos_182.variants.janzer_sudakov : ∀ k : ℕ, 3 ≤ k →
    (fun n : ℕ ↦ (f n k : ℝ)) =Θ[atTop] fun n ↦ (n : ℝ) * Real.log (Real.log n) := by
  sorry

/--
Chakraborti, Janzer, Methuku, and Montgomery [CJMM24b] have shown that one can take
$C(k)\ll k^2$, which is the best possible up to an absolute constant.
-/
@[category research solved, AMS 5]
theorem erdos_182.variants.cjmm : ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k →
    ∀ᶠ n : ℕ in atTop, (f n k : ℝ) ≤ C * k ^ 2 * n * Real.log (Real.log n) := by
  sorry

end Erdos182
