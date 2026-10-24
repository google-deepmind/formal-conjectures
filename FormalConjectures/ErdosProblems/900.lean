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
# Erdős Problem 900

*References:*
- [erdosproblems.com/900](https://www.erdosproblems.com/900)
- [AKS81] Ajtai, Miklós and Komlós, János and Szemerédi, Endre, *The longest path in a random
  graph*. Combinatorica 1 (1981), 1--12.
- [Er78] Erdős, Paul, *Problems and results in combinatorial analysis and combinatorial number
  theory*. Proceedings of the Ninth Southeastern Conference on Combinatorics, Graph Theory, and
  Computing (1978), 29-40. [PDF](https://www.renyi.hu/~p_erdos/1978-36.pdf)
-/

@[expose] public section

open Filter SimpleGraph
open scoped Topology

namespace Erdos900

/-- The probability that a graph chosen uniformly at random among the graphs on the vertex set
`Fin n` with exactly `m` edges satisfies `P`. If `n.choose 2 < m` there is no such graph, and
the value is `0` (the quotient is $0/0$). -/
noncomputable def uniformEdgeProbability (n m : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (Set.ncard {G : SimpleGraph (Fin n) | G.edgeSet.ncard = m ∧ P G} : ℝ) /
    ((n.choose 2).choose m : ℝ)

/-- `HasLongPath n a G` says that the graph `G` on `Fin n` contains a path with at least $an$
edges. That is, `G` contains a copy of the path graph on `⌈a * n⌉₊ + 1` vertices. -/
def HasLongPath (n : ℕ) (a : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  pathGraph (⌈a * n⌉₊ + 1) ⊑ G

/-- If $m > \binom{n}{2}$ then no graph on `Fin n` has $m$ edges, and the probability is `0`. -/
@[category API, AMS 5 60]
theorem uniformEdgeProbability_of_lt (n m : ℕ) (P : SimpleGraph (Fin n) → Prop)
    (h : n.choose 2 < m) : uniformEdgeProbability n m P = 0 := by
  simp [uniformEdgeProbability, Nat.choose_eq_zero_of_lt h]

/--
There is a function $f:(1/2,\infty)\to \mathbb{R}$ such that $f(c)\to 0$ as $c\to 1/2$ and
$f(c)\to 1$ as $c\to \infty$ and every random graph with $n$ vertices and $cn$ edges has (with
high probability) a path of length at least $f(c)n$.

Conjectured by Erdős [Er78, p. 32] and proved by Ajtai, Komlós, and Szemerédi [AKS81]. We take
the uniform random graph with $\lfloor cn\rfloor$ edges, count the length of a path in edges, read
"with high probability" as probability tending to $1$ as $n\to\infty$, and require $f(c)>0$ for
every $c>1/2$ (a path of linear length). The linked formal proof uses the same uniform model,
written as uniformly random $0/1$ vectors of weight $\lfloor cn\rfloor$ indexed by the pairs of
vertices.
-/
@[category research solved, AMS 5 60, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos900.lean#L950"]
theorem erdos_900 :
    ∃ f : ℝ → ℝ, (∀ c : ℝ, 1 / 2 < c → 0 < f c) ∧
      Tendsto f (𝓝[>] (1 / 2)) (𝓝 0) ∧ Tendsto f atTop (𝓝 1) ∧
      ∀ c : ℝ, 1 / 2 < c → Tendsto (fun n : ℕ ↦
        uniformEdgeProbability n ⌊c * n⌋₊ (HasLongPath n (f c))) atTop (𝓝 1) := by
  sorry

end Erdos900
