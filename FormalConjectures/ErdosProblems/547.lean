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
# Erdős Problem 547

*Reference:* [erdosproblems.com/547](https://www.erdosproblems.com/547)

If $T$ is a tree on $n$ vertices then $R(T) \leq 2n - 2$.

This was conjectured by Burr and Erdős [BuEr76]. It follows from the Erdős–Sós
conjecture [548], and has been proved for all large $n$ by Zhao [Zh11].

[BuEr76] Burr, S. A. and Erdős, P. (1976).

[Zh11] Zhao, Y. (2011).
-/

open SimpleGraph

namespace Erdos547

/-- A graph $H$ contains a copy of graph $G$ (as a subgraph) if there is an injective
function from $V(G)$ to $V(H)$ that preserves adjacency. -/
def ContainsSubgraphCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The diagonal Ramsey number $R(G)$ for a graph $G$ on $\operatorname{Fin}(k)$: the minimum $N$
such that every graph $H$ on $N$ vertices contains a copy of $G$ or its complement contains
a copy of $G$. -/
noncomputable def ramseyNumber {k : ℕ} (G : SimpleGraph (Fin k)) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    ContainsSubgraphCopy G H ∨ ContainsSubgraphCopy G Hᶜ}

/--
Erdős Problem 547 [BuEr76]:

If $T$ is a tree on $n$ vertices then $R(T) \leq 2n - 2$.
-/
@[category research open, AMS 5]
theorem erdos_547 (n : ℕ) (hn : n ≥ 2)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    ramseyNumber T ≤ 2 * n - 2 := by
  sorry

end Erdos547
