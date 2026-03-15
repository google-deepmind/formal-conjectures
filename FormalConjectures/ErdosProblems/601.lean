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
# Erdős Problem 601

*Reference:* [erdosproblems.com/601](https://www.erdosproblems.com/601)

For which limit ordinals $\alpha$ is it true that if $G$ is a graph with vertex set $\alpha$
then $G$ must have either an infinite path or an independent set on a set of
vertices with order type $\alpha$?

A problem of Erdős, Hajnal, and Milner, who proved this is true for
$\alpha < \omega_1^{\omega+2}$. Erdős offered 250 dollars for showing what happens when
$\alpha = \omega_1^{\omega+2}$ and 500 dollars for settling the general case.
Larson proved this is true for all $\alpha < 2^{\aleph_0}$ assuming Martin's axiom.

[EHM70] Erdős, P., Hajnal, A., and Milner, E.C., _A theorem in the partition calculus_,
Acta Math. Acad. Sci. Hungar. 21 (1970), 335–357.

[Er81] Erdős, P., _Solved and unsolved problems in combinatorics and combinatorial
number theory_, Congr. Numer. 32 (1981), 49–62.

[Er82e] Erdős, P., _Problems and results on finite and infinite combinatorial analysis II_,
L'Enseignement Math. 27 (1982), 163–176.

[Er87] Erdős, P., _Some problems on finite and infinite graphs_, Logic and combinatorics,
Contemp. Math. 65 (1987), 223–228.

[La90] Larson, J.A., _Martin's axiom and ordinal graphs: large independent sets or infinite
paths_, Ann. Pure Appl. Logic (1990), 31–39.
-/

open SimpleGraph Ordinal

namespace Erdos601

/-- The type of ordinals strictly less than $\alpha$. -/
abbrev OrdinalSet (α : Ordinal) := {a : Ordinal // a < α}

/-- A graph has an infinite path: an injective sequence of vertices
such that consecutive vertices are adjacent. -/
def HasInfinitePath {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : ℕ → V, Function.Injective f ∧ ∀ n : ℕ, G.Adj (f n) (f (n + 1))

/-- A graph on `OrdinalSet α` has an independent set of order type $\alpha$:
there is an order embedding from `OrdinalSet α` into itself whose
image is an independent set. -/
def HasIndepSetOfOrderType {α : Ordinal}
    (G : SimpleGraph (OrdinalSet α)) : Prop :=
  ∃ e : OrdinalSet α ↪o OrdinalSet α,
    ∀ i j : OrdinalSet α, i ≠ j → ¬G.Adj (e i) (e j)

/-- The Erdős-Hajnal-Milner property for an ordinal $\alpha$:
every graph on vertex set $\alpha$ has either an infinite path or
an independent set of order type $\alpha$. -/
def EHMProperty (α : Ordinal) : Prop :=
  ∀ G : SimpleGraph (OrdinalSet α),
    HasInfinitePath G ∨ HasIndepSetOfOrderType G

/--
Erdős Problem 601 [EHM70] [Er81] [Er82e] [Er87]:

Every limit ordinal has the Erdős-Hajnal-Milner property: if $G$ is a graph
with vertex set $\alpha$ (a limit ordinal), then $G$ must have either an infinite path
or an independent set of vertices with order type $\alpha$.

Known results:
- True for $\alpha < \omega_1^{\omega+2}$ (Erdős-Hajnal-Milner, 1970)
- True for all $\alpha < 2^{\aleph_0}$ assuming Martin's axiom (Larson, 1990)
-/
@[category research open, AMS 3 5]
theorem erdos_601 (α : Ordinal) (hα : Order.IsSuccLimit α) :
    EHMProperty α := by
  sorry

end Erdos601
