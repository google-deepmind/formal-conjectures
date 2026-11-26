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
# Size of bridgeless graphs that forces an orientation of small diameter

*Reference:* [arxiv/2508.17569](https://arxiv.org/abs/2508.17569)
**A Size Condition for Small Diameter Orientable Graphs**
by *Sopon Boriboon and Teeradej Kittipassorn*

For $2 \le d \le n - 2$, let $m(n,d)$ be the least $M$ such that every bridgeless graph of
order $n$ and size at least $M$ has an orientation of diameter at most $d$. Conjecture 4 of
the paper states $m(n,d) = \binom{n-d}{2} + n + 2$. This fails at $(n,d) = (7,3)$, where
$m(7,3) = 14$ instead of $15$, and at $(n,d) = (7,4)$, where $m(7,4) = 11$ instead of $12$.
In particular, for $n = 7$ and $d \in \{3, 4\}$ there is no graph of the kind asked for in
Problem 7 of the paper.
-/

@[expose] public section

namespace Arxiv.«2508.17569»

open SimpleGraph

variable {V : Type*}

/-- A graph is bridgeless if it is connected and has no bridge. -/
def IsBridgeless (G : SimpleGraph V) : Prop := G.Connected ∧ ∀ e, ¬ G.IsBridge e

/-- `relPow r k u v`: there is a directed walk of length exactly `k` from `u` to `v`. -/
def relPow (r : V → V → Prop) : ℕ → V → V → Prop
  | 0 => fun u v => u = v
  | k + 1 => fun u w => ∃ v, relPow r k u v ∧ r v w

/-- `G` has an orientation of diameter at most `d`. -/
def HasOrientedDiameterLE (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ D : Digraph V, D.IsOrientation G ∧ ∀ u v, ∃ k ≤ d, relPow D.Adj k u v

/-- $m(n,d)$: the least $M$ such that every bridgeless graph of order $n$ and size at
least $M$ has an orientation of diameter at most $d$. -/
noncomputable def minEdges (n d : ℕ) : ℕ :=
  sInf {M : ℕ | ∀ G : SimpleGraph (Fin n), IsBridgeless G → M ≤ G.edgeSet.ncard →
    HasOrientedDiameterLE G d}

set_option linter.style.formal_proof_palomar false in
/--
Conjecture 4 of Boriboon and Kittipassorn states that $m(n,d) = \binom{n-d}{2} + n + 2$ for
all $2 \le d \le n - 2$. The conjecture is false: $m(7,3) = 14$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/derekblair/math-proofs/blob/3e404e229a3ffe04057f84d7379e3bb9d34b19f8/research/graph-conjecture-results-2026-11-25/boriboon-kittipassorn-conj4/BK73Answer.lean#L51"]
theorem conjecture_4 :
    ¬ ∀ n d : ℕ, 2 ≤ d → d ≤ n - 2 → minEdges n d = (n - d).choose 2 + n + 2 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- $m(7,3) = 14$, while Conjecture 4 predicts $15$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/derekblair/math-proofs/blob/3e404e229a3ffe04057f84d7379e3bb9d34b19f8/research/graph-conjecture-results-2026-11-25/boriboon-kittipassorn-conj4/BK73Answer.lean#L55"]
theorem conjecture_4.variants.seven_three : minEdges 7 3 = 14 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- $m(7,4) = 11$, while Conjecture 4 predicts $12$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/derekblair/math-proofs/blob/3e404e229a3ffe04057f84d7379e3bb9d34b19f8/research/graph-conjecture-results-2026-11-25/boriboon-kittipassorn-conj4/BK73Answer.lean#L58"]
theorem conjecture_4.variants.seven_four : minEdges 7 4 = 11 := by
  sorry

end Arxiv.«2508.17569»
