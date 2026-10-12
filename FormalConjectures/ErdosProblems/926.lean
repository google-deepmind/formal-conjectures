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
# Erdős Problem 926

*References:*
- [erdosproblems.com/926](https://www.erdosproblems.com/926)
- [Er69b] Erdős, P., *Problems and results in chromatic graph theory*. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er74c] Erdős, Paul, *Extremal problems on graphs and hypergraphs*. (1974), 75-84.
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [Fu91] Füredi, Zoltán, *On a Turán type problem of Erdős*. Combinatorica (1991), 75--79.
- [AKS03] Alon, Noga and Krivelevich, Michael and Sudakov, Benny, *Turán numbers of bipartite
  graphs and related Ramsey-type questions*. Combin. Probab. Comput. (2003), 477-494.
-/

@[expose] public section

open Filter Asymptotics SimpleGraph

namespace Erdos926

/-- The graph $H_k$ on the vertices $x, y_1, \ldots, y_k, z_{ij}$ ($i < j$): $x$ is adjacent to
every $y_i$, and each pair $y_i, y_j$ is adjacent to the vertex $z_{ij}$. -/
def H (k : ℕ) : SimpleGraph (Unit ⊕ (Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2})) where
  Adj x y :=
    match x, y with
    | Sum.inl _, Sum.inr (Sum.inl _) => True
    | Sum.inr (Sum.inl _), Sum.inl _ => True
    | Sum.inr (Sum.inl i), Sum.inr (Sum.inr p) => i = p.1.1 ∨ i = p.1.2
    | Sum.inr (Sum.inr p), Sum.inr (Sum.inl i) => i = p.1.1 ∨ i = p.1.2
    | _, _ => False
  symm := by
    constructor
    intro x y h
    rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> simp_all
  loopless := by
    constructor
    intro x
    rcases x with _ | _ | _ <;> simp

/--
Let $k\geq 4$. Is it true that
$$\mathrm{ex}(n;H_k) \ll_k n^{3/2},$$
where $H_k$ is the graph on vertices $x,y_1,\ldots,y_k,z_1,\ldots,z_{\binom{k}{2}}$, where $x$ is
adjacent to all $y_i$ and each pair of $y_i,y_j$ is adjacent to a unique $z_i$.

It is trivial that $\mathrm{ex}(n;H_k)\gg n^{3/2}$ since $H_k$ contians a $C_4$ for $k\geq 3$.
Erdős [Er71] claimed a proof for $k=3$.

The answer is yes, proved by Füredi [Fu91], who proved that $\mathrm{ex}(n;H_k) \ll (kn)^{3/2}$.
This was improved to $\mathrm{ex}(n;H_k) \ll kn^{3/2}$ by Alon, Krivelevich, and Sudakov [AKS03].

Since each $H_k$ is 2-degenerate this is a special case of [146](https://www.erdosproblems.com/146).
The extremal number of the graph $H_k$ with the vertex $x$ omitted is the subject of
[1021](https://www.erdosproblems.com/1021).
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos926.lean#L644"]
theorem erdos_926 : answer(True) ↔ ∀ k : ℕ, 4 ≤ k →
    (fun n : ℕ => (extremalNumber n (H k) : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) := by
  sorry

/-- Alon, Krivelevich, and Sudakov [AKS03] proved $\mathrm{ex}(n;H_k) \ll kn^{3/2}$ with an
absolute implied constant. -/
@[category research solved, AMS 5]
theorem erdos_926.variants.aks : ∃ C : ℝ, ∀ k : ℕ, 4 ≤ k → ∀ n : ℕ,
    (extremalNumber n (H k) : ℝ) ≤ C * k * (n : ℝ) ^ (3 / 2 : ℝ) := by
  sorry

end Erdos926
