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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1080

*References:*
- [erdosproblems.com/1080](https://www.erdosproblems.com/1080)
- [DeSz92] de Caen, D. and Székely, L. A., The maximum size of {$4$}- and {$6$}-cycle free bipartite
  graphs on {$m,n$} vertices. (1992), 135--142.
- [Er75] Erdős, P., Some recent progress on extremal problems in graph theory. Congr. Numer. (1975),
  3-14.
- [LUW94] Lazebnik, F. and Ustimenko, V. A. and Woldar, A. J., New constructions of bipartite graphs
  on {$m,n$} vertices with many edges and without small cycles. J. Combin. Theory Ser. B (1994),
  111--117.
-/

open SimpleGraph

namespace Erdos1080

/-- `IsBipartition G X Y` means that `X` and `Y` form a bipartition of the vertices of `G`. -/
def IsBipartition {V : Type*} (G : SimpleGraph V) (X Y : Set V) : Prop :=
  Disjoint X Y ∧ X ∪ Y = Set.univ ∧ ∀ ⦃u v⦄, G.Adj u v → (u ∈ X ↔ v ∈ Y)

/--
Let $G$ be a bipartite graph on $n$ vertices such that one part has $\lfloor n^{2/3}\rfloor$
vertices. Is there a constant $c>0$ such that if $G$ has at least $cn$ edges then $G$ must
contain a $C_6$?

The answer is no, as shown by De Caen and Székely [DeSz92], who in fact show a stronger result.
Let $f(n,m)$ be the maximum number of edges of a bipartite graph between $n$ and $m$ vertices which
does not contain either a $C_4$ or $C_6$. A positive answer to this question would then imply
$f(n,\lfloor n^{2/3}\rfloor)\ll n$. De Caen and Székely prove
$n^{10/9}\gg f(n,\lfloor n^{2/3}\rfloor) \gg n^{58/57+o(1)}$ for $m\sim n^{2/3}$. They also prove
more generally that, for $n^{1/2}\leq m\leq n$, $f(n,m) \ll (nm)^{2/3},$ which was also proved by
Faudree and Simonovits.

This was formalized in Lean by Alexeev using Aristotle.
-/
@[category research formally solved using lean4 at
"https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos1080.lean", AMS 5]
theorem erdos_1080 :
    answer(False) ↔
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y → X.ncard = ⌊(Fintype.card V : ℝ) ^ (2/3 : ℝ)⌋₊ →
      G.edgeSet.ncard ≥ c * Fintype.card V →
        ∃ (v : V) (walk : G.Walk v v), walk.IsCycle ∧ walk.length = 6 := by
  sorry

-- TODO: Add Erdos C_8 variant.
-- TODO: Add Lazebnik, Ustimenko, and Woldar's lower bound.

end Erdos1080
