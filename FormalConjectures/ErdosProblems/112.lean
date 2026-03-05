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
# Erdős Problem 112

*Reference:* [erdosproblems.com/112](https://www.erdosproblems.com/112)

A problem of Erdős and Rado on directed Ramsey numbers $k(n,m)$: the minimal $k$ such that
any directed graph on $k$ vertices must contain either an independent set of size $n$ or a
transitive tournament of size $m$. Determine $k(n,m)$.

[ErRa67] Erdős, P. and Rado, R., _Partition relations and transitivity domains of binary
relations_, J. London Math. Soc. (1967).

[LaMi97] Larson, J. and Mitchell, W., _On a problem of Erdős and Rado_, Ann. Comb. (1997).
-/

namespace Erdos112

/-- A directed graph on vertex type $V$: an irreflexive binary relation representing
directed edges ($\mathrm{adj}(u, v)$ means there is a directed edge from $u$ to $v$). -/
structure Digraph (V : Type*) where
  adj : V → V → Prop
  loopless : ∀ v, ¬ adj v v

/-- An independent set in a directed graph: a set $S$ of vertices with no directed
edges between any two of its members (in either direction). -/
def Digraph.IsIndepSet {V : Type*} (G : Digraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.adj u v

/-- A transitive tournament on vertex set $S$ in directed graph $G$: there is a bijection
$f : \mathrm{Fin}(|S|) \to S$ such that $G.\mathrm{adj}(f(i), f(j))$ holds
if and only if $i < j$. This encodes a total ordering of $S$ compatible with the
edge relation. -/
def Digraph.IsTransTournament {V : Type*} (G : Digraph V) (S : Finset V) : Prop :=
  ∃ f : Fin S.card → {x : V // x ∈ S}, Function.Bijective f ∧
    ∀ i j : Fin S.card, G.adj (f i : V) (f j : V) ↔ i < j

/-- The directed Ramsey number $k(n,m)$: the minimal $k$ such that every directed graph
on $k$ vertices contains either an independent set of size $n$ or a transitive
tournament of size $m$. -/
noncomputable def dirRamseyNum (n m : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (V : Type) [Fintype V], Fintype.card V = k →
    ∀ G : Digraph V,
      (∃ S : Finset V, S.card = n ∧ G.IsIndepSet S) ∨
      (∃ S : Finset V, S.card = m ∧ G.IsTransTournament S)}

/--
Erdős Problem 112: Determine the directed Ramsey number $k(n,m)$.
The exact value is still open.
-/
@[category research open, AMS 5]
theorem erdos_112 :
    ∀ n m : ℕ, 2 ≤ n → 2 ≤ m →
      dirRamseyNum n m = answer(sorry) := by
  sorry

/--
Erdős–Rado upper bound [ErRa67]:
$$k(n,m) \leq \frac{2^{m-1} (n-1)^m + n - 2}{2n - 3}.$$
-/
@[category research solved, AMS 5]
theorem erdos_112.variants.erdos_rado_upper_bound :
    ∀ n m : ℕ, 2 ≤ n → 2 ≤ m →
      dirRamseyNum n m ≤ (2 ^ (m - 1) * (n - 1) ^ m + n - 2) / (2 * n - 3) := by
  sorry

/--
Larson–Mitchell bound [LaMi97]: $k(n, 3) \leq n^2$.
-/
@[category research solved, AMS 5]
theorem erdos_112.variants.larson_mitchell :
    ∀ n : ℕ, 2 ≤ n →
      dirRamseyNum n 3 ≤ n ^ 2 := by
  sorry

end Erdos112
