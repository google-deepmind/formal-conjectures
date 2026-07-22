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

import FormalConjecturesUtil

/-!
# Erdős Problem 775

*References:*
- [erdosproblems.com/775](https://www.erdosproblems.com/775)
- [Ga25] Gao, J., *On cliques in hypergraphs*. arXiv:2510.14804 (2025).
- [MoMo65] Moon, J. W. and Moser, L., *On cliques in graphs*. Israel J. Math. (1965), 23-28.
- [Sp71] Spencer, J. H., *On cliques in graphs*. Israel J. Math. (1971), 419-421.
-/

open Filter

namespace Erdos775

/-- A finite set of vertices `S` spans a *complete subgraph* of the 3-uniform hypergraph `H`
when every 3-element subset of `S` is an edge of `H`. -/
def IsCompleteSubgraph {V : Type} (H : ThreeUniformHypergraph V) (S : Finset V) : Prop :=
  ∀ e : Finset V, e ⊆ S → e.card = 3 → e ∈ H.edges

/-- The set of sizes of the cliques (maximal complete subgraphs) of a 3-uniform
hypergraph `H`. -/
def cliqueSizes {V : Type} (H : ThreeUniformHypergraph V) : Set ℕ :=
  { k | ∃ S : Finset V, Maximal (IsCompleteSubgraph H) S ∧ S.card = k }

/-- The set of sizes of the cliques (maximal complete subgraphs) of a simple graph `G`. -/
def graphCliqueSizes {V : Type} (G : SimpleGraph V) : Set ℕ :=
  { k | ∃ S : Finset V, Maximal (fun T : Finset V => G.IsClique (T : Set V)) S ∧ S.card = k }

/--
Is there a $3$-uniform hypergraph on $n$ vertices which contains at least $n-O(1)$ different
sizes of cliques (maximal complete subgraphs)?

The answer is no, as proved by Gao [Ga25]: more generally, for any $k\geq 3$, every $k$-uniform
hypergraph on $n$ vertices contains at most $n-f_k(n)$ different sizes of cliques, where
$f_k(n)\to \infty$ as $n\to \infty$.
-/
@[category research solved, AMS 5]
theorem erdos_775 : answer(False) ↔
    ∃ C : ℕ, ∃ᶠ n : ℕ in atTop, ∃ H : ThreeUniformHypergraph (Fin n),
      n - C ≤ (cliqueSizes H).ncard := by
  sorry

/--
The answer is no, as proved by Gao [Ga25]: more generally, for any $k\geq 3$, every $k$-uniform
hypergraph on $n$ vertices contains at most $n-f_k(n)$ different sizes of cliques, where
$f_k(n)\to \infty$ as $n\to \infty$.
-/
@[category research solved, AMS 5]
theorem erdos_775.variants.gao :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      ∀ᶠ n : ℕ in atTop, ∀ H : ThreeUniformHypergraph (Fin n),
        (cliqueSizes H).ncard + f n ≤ n := by
  sorry

/--
For graphs, Spencer [Sp71] constructed a graph which contains cliques of at least
$n-\log_2n+O(1)$ different sizes.
-/
@[category research solved, AMS 5]
theorem erdos_775.variants.spencer :
    ∃ C : ℝ, ∀ n : ℕ, ∃ G : SimpleGraph (Fin n),
      (n : ℝ) - Real.logb 2 (n : ℝ) - C ≤ ((graphCliqueSizes G).ncard : ℝ) := by
  sorry

/--
For graphs, Spencer [Sp71] constructed a graph which contains cliques of at least
$n-\log_2n+O(1)$ different sizes, which Moon and Moser [MoMo65] showed to be best possible.
-/
@[category research solved, AMS 5]
theorem erdos_775.variants.moon_moser :
    ∃ C : ℝ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      ((graphCliqueSizes G).ncard : ℝ) ≤ (n : ℝ) - Real.logb 2 (n : ℝ) + C := by
  sorry

end Erdos775
