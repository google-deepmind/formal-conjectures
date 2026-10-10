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
# Erdős Problem 1021

*References:*
- [erdosproblems.com/1021](https://www.erdosproblems.com/1021)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er74c] Erdős, Paul, *Extremal problems on graphs and hypergraphs*. (1974), 75-84.
- [CoLe21] Conlon, David and Lee, Joonkyung, *On the extremal number of subdivisions*. Int. Math.
  Res. Not. IMRN (2021), 9122--9145.
- [Ja19] Janzer, Oliver, *Improved bounds for the extremal number of subdivisions*. Electron. J.
  Combin. (2019), Paper No. 3.3, 6.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1021

/-- The graph `G_k`: the bipartite graph between `{y_1, …, y_k}` (the elements of `Fin k`) and
`{z_1, …, z_{k choose 2}}` (the two-element subsets of `Fin k`), each `z` being joined to the two
elements of the corresponding pair. This is the `1`-subdivision of `K_k`. -/
def cliqueSubdivision (k : ℕ) : SimpleGraph (Fin k ⊕ Set.powersetCard (Fin k) 2) where
  Adj x y :=
    match x, y with
    | Sum.inl i, Sum.inr p => i ∈ (p : Finset (Fin k))
    | Sum.inr p, Sum.inl i => i ∈ (p : Finset (Fin k))
    | _, _ => False
  symm := by
    constructor
    intro x y h
    cases x <;> cases y <;> simp_all
  loopless := by
    constructor
    intro x
    cases x <;> simp

/--
Is it true that, for every $k \geq 3$, there is a constant $c_k > 0$ such that
$$\mathrm{ex}(n, G_k) \ll n^{3/2 - c_k},$$
where $G_k$ is the bipartite graph between $\{y_1, \ldots, y_k\}$ and
$\{z_1, \ldots, z_{\binom{k}{2}}\}$, with each $z_j$ joined to a unique pair of $y_i$?

A conjecture of Erdős and Simonovits [Er71, Er74c], who proved (in unpublished work) that one must
have $c_k \to 0$ as $k \to \infty$. The graph $G_k$ is the $1$-subdivision of $K_k$; for $k = 3$
it is the $6$-cycle. This was proved by Conlon and Lee [CoLe21] with $c_k = 6^{-k}$, improved to
$c_k = \frac{1}{4k - 6}$ by Janzer [Ja19]; see `erdos_1021.variants.janzer`.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1021.lean#L2359"]
theorem erdos_1021 : answer(True) ↔
    ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 < c ∧
      (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
        fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - c) := by
  sorry

/-- Janzer [Ja19] proved that one can take $c_k = \frac{1}{4k - 6}$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1021.lean#L2336"]
theorem erdos_1021.variants.janzer (k : ℕ) (hk : 3 ≤ k) :
    (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6)) := by
  sorry

end Erdos1021
