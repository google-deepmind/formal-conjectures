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
# Sumner's universal tournament conjecture (1971)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Sumner%27s_conjecture)
* [HT91] Häggkvist, R. and Thomason, A. (1991). "Trees in tournaments." *Combinatorica* 11,
  pp. 123--130.
* [ES04] El Sahili, A. (2004). "Trees in tournaments." *J. Combin. Theory Ser. B* 92,
  pp. 183--187.
* [KMO11] Kühn, D., Mycroft, R. and Osthus, D. (2011). "A proof of Sumner's universal
  tournament conjecture for large tournaments." *Proc. London Math. Soc.* 102, pp. 731--766.
  [arXiv:1010.4430](https://arxiv.org/abs/1010.4430)
-/

open SimpleGraph Digraph

namespace SumnerUniversalTournamentConjecture

/-- An **oriented tree**: a digraph that is an orientation of a tree. -/
def IsOrientedTree {W : Type*} (D : Digraph W) : Prop :=
  ∃ T : SimpleGraph W, T.IsTree ∧ D.IsOrientation T

/-- The digraph `D` **embeds** in `D'`: there is an injective digraph homomorphism `D →g D'`. -/
def Embeds {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    (D : Digraph W) (D' : Digraph V) : Prop :=
  ∃ f : D →g D', Function.Injective f

/--
**Sumner's universal tournament conjecture (1971).**

Every tournament on $2n - 2$ vertices contains every oriented tree on $n \ge 2$ vertices as a
subgraph.
-/
@[category research open, AMS 5]
theorem sumner_conjecture :
    ∀ (n : ℕ), 2 ≤ n →
      ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
        Fintype.card W = n → IsOrientedTree D →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
          Fintype.card V = 2 * n - 2 → G.IsTournament → Embeds D G := by
  sorry

/--
**Kühn–Mycroft–Osthus (2011): the conjecture holds for all sufficiently large $n$.**

*Reference:* [KMO11].
-/
@[category research solved, AMS 5]
theorem sumner_conjecture.variants.large_n :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
      ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
        Fintype.card W = n → IsOrientedTree D →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
          Fintype.card V = 2 * n - 2 → G.IsTournament → Embeds D G := by
  sorry

/--
**El Sahili (2004): tournaments on $3n - 3$ vertices suffice.**

Every tournament on $3n - 3$ vertices contains every oriented tree on $n \ge 2$ vertices,
improving the bound $12n$ of Häggkvist and Thomason [HT91].

*Reference:* [ES04].
-/
@[category research solved, AMS 5]
theorem sumner_conjecture.variants.el_sahili (n : ℕ) (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hD : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 3 * n - 3) (hG : G.IsTournament) : Embeds D G := by
  sorry

/--
**The bound $2n - 2$ would be sharp.**

For every $n \ge 2$ there is an oriented tree on $n$ vertices — the out-star, with arcs from a
centre to the $n - 1$ other vertices — that embeds in no regular tournament on $2n - 3$ vertices:
every vertex of such a tournament has out-degree $n - 2 < n - 1$.
-/
@[category research solved, AMS 5]
theorem sumner_conjecture.variants.sharp (n : ℕ) (hn : 2 ≤ n) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G := by
  sorry

end SumnerUniversalTournamentConjecture
