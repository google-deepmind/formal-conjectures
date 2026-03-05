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
# Erdős Problem 629

*Reference:* [erdosproblems.com/629](https://www.erdosproblems.com/629)

Determine the minimal number of vertices $n(k)$ of a bipartite graph $G$ such that
the list chromatic number $\chi_L(G) > k$.

A problem of Erdős, Rubin, and Taylor [ERT80], who proved that
$2^{k-1} < n(k) < k^2 \cdot 2^{k+2}$
and $n(2) = 6$. Hanson, MacGillivray, and Toft [HMT96] proved $n(3) = 14$.

[ERT80] Erdős, P., Rubin, A. L., and Taylor, H., _Choosability in graphs_,
Proc. West Coast Conf. on Combinatorics, Graph Theory and Computing,
Congressus Numerantium XXVI (1980), 125-157.

[HMT96] Hanson, D., MacGillivray, G., and Toft, B., _Choosability of bipartite graphs_,
Ars Combinatoria 44 (1996), 183-192.
-/

open SimpleGraph

namespace Erdos629

/-- A proper list coloring of $G$ with respect to a list assignment $L : V \to \text{Finset}\ \mathbb{N}$
is a function $f : V \to \mathbb{N}$ such that $f(v) \in L(v)$ for all $v$, and $f(u) \neq f(v)$
whenever $u$ and $v$ are adjacent. -/
def IsProperListColoring {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ)
    (f : V → ℕ) : Prop :=
  (∀ v, f v ∈ L v) ∧ (∀ u v, G.Adj u v → f u ≠ f v)

/-- A graph $G$ is $k$-choosable ($k$-list-colorable) if for every list assignment $L$
where each vertex receives a list of at least $k$ colors, there exists a
proper list coloring. -/
def IsChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) →
    ∃ f : V → ℕ, IsProperListColoring G L f

/-- The list chromatic number (choice number) of a graph $G$: the minimum $k$
such that $G$ is $k$-choosable. -/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsChoosable G k}

/-- $n(k)$: the minimum number of vertices of a bipartite graph with list
chromatic number greater than $k$. -/
noncomputable def erdos629_n (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ G : SimpleGraph (Fin n),
    G.Colorable 2 ∧ listChromaticNumber G > k}

/--
Erdős Problem 629, lower bound [ERT80]:
$2^{k-1} < n(k)$ for all $k \geq 1$.
-/
@[category research solved, AMS 5]
theorem erdos_629 (k : ℕ) (hk : k ≥ 1) :
    erdos629_n k > 2 ^ (k - 1) := by
  sorry

/--
Erdős Problem 629, upper bound [ERT80]:
$n(k) < k^2 \cdot 2^{k+2}$ for all $k \geq 1$.
-/
@[category research solved, AMS 5]
theorem erdos_629.variants.upper_bound (k : ℕ) (hk : k ≥ 1) :
    erdos629_n k < k ^ 2 * 2 ^ (k + 2) := by
  sorry

/--
Erdős Problem 629 [ERT80]: $n(2) = 6$.
-/
@[category research solved, AMS 5]
theorem erdos_629.variants.n2 : erdos629_n 2 = 6 := by
  sorry

/--
Erdős Problem 629 [HMT96]: $n(3) = 14$.
-/
@[category research solved, AMS 5]
theorem erdos_629.variants.n3 : erdos629_n 3 = 14 := by
  sorry

end Erdos629
