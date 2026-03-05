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
# Erdős Problem 1157

*Reference:* [erdosproblems.com/1157](https://www.erdosproblems.com/1157)

Let $r \geq 2$. Let $F$ be the family of all $r$-uniform hypergraphs with $k$ vertices
and $s$ edges. Determine $\mathrm{ex}_r(n, F)$.

Here $\mathrm{ex}_r(n, F) = f_r(n; k, s)$, the maximum number of edges in an $r$-uniform
hypergraph on $n$ vertices such that no $k$ vertices span $s$ or more edges.

Known lower bound (Brown, Erdős, Sós [BES73]): for all $k > r$ and $s > 1$,
$$f_r(n; k, s) \gg n^{(rs-k)/(s-1)}.$$

The general conjecture of Brown, Erdős, and Sós is that, for all $r > t \geq 2$
and $s \geq 3$,
$$f_r(n; k, s) = o(n^t)$$
whenever $k \geq (r - t)s + t + 1$.

The case $t = 2$ is problem [1178]. The case $r = 3$, $k = 6$, $s = 3$ is problem [716]
(proved by Ruzsa–Szemerédi). The case $r = 3$ and $k = s + 2$ is problem [1076].

[BES73] Brown, W.G., Erdős, P., and Sós, V.T., *Some extremal problems on r-graphs*,
New Directions in the Theory of Graphs (1973).

[Va99] See erdosproblems.com/1157.
-/

open Finset

namespace Erdos1157

/-- An $r$-uniform hypergraph on $n$ vertices: a family of $r$-element subsets of
$\operatorname{Fin}(n)$. -/
structure UniformHypergraph (r n : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = r

/-- The number of edges of $H$ spanned by a set $S$ of vertices. -/
def edgesSpannedBy {r n : ℕ} (H : UniformHypergraph r n) (S : Finset (Fin n)) : ℕ :=
  (H.edges.filter (· ⊆ S)).card

/-- $H$ is $(k,s)$-free if no set of $k$ vertices spans $s$ or more edges. -/
def IsFree {r n : ℕ} (H : UniformHypergraph r n) (k s : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → edgesSpannedBy H S < s

/-- $f_r(n; k, s)$: the maximum number of edges in an $r$-uniform $(k,s)$-free
hypergraph on $n$ vertices. -/
noncomputable def extremalNumber (r n k s : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : UniformHypergraph r n, IsFree H k s ∧ H.edges.card = m}

/--
Erdős Problem #1157 — Brown–Erdős–Sós Conjecture (general form) [BES73, Va99]:

For all $r > t \geq 2$, $s \geq 3$, and $k \geq (r - t) \cdot s + t + 1$, we have
$$f_r(n; k, s) = o(n^t),$$
i.e., for every $\varepsilon > 0$, for all sufficiently large $n$,
$$f_r(n; k, s) \leq \varepsilon \cdot n^t.$$
-/
@[category research open, AMS 5]
theorem erdos_1157 (r t : ℕ) (hr : r > t) (ht : t ≥ 2)
    (s : ℕ) (hs : s ≥ 3) (k : ℕ) (hk : k ≥ (r - t) * s + t + 1) :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (extremalNumber r n k s : ℝ) ≤ ε * (n : ℝ) ^ t := by
  sorry

end Erdos1157
