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
# Erdős Problem 919

*Reference:* [erdosproblems.com/919](https://www.erdosproblems.com/919)

This question was inspired by a theorem of Babai, that if $G$ is a graph on a
well-ordered set with chromatic number $\geq \aleph_0$ there is a subgraph on
vertices with order-type $\omega$ with chromatic number $\aleph_0$.

Erdős and Hajnal showed this does not generalise to higher cardinals — they
constructed a graph on $\omega_1^2$ with chromatic number $\aleph_1$ such that
every strictly smaller subgraph has chromatic number $\leq \aleph_0$.

A similar construction produces a graph on $\omega_2^2$ with chromatic number
$\aleph_2$ such that every smaller subgraph has chromatic number $\leq \aleph_1$.

[Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof Techniques in Graph
Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
-/

open SimpleGraph Cardinal Ordinal
open scoped Cardinal

namespace Erdos919

/--
Erdős Problem 919 [Er69b]:

Is there a graph on a well-ordered set of order type $\omega_2 \cdot \omega_2$ with chromatic
number $\aleph_2$ such that every subgraph induced on a subset of strictly smaller
order type has chromatic number $\leq \aleph_0$?
-/
@[category research open, AMS 3 5]
theorem erdos_919 : answer(sorry) ↔
    ∃ (V : Type) (_ : LinearOrder V) (_ : IsWellOrder V (· < ·))
      (G : SimpleGraph V),
      Ordinal.type ((· < ·) : V → V → Prop) =
        Cardinal.ord (aleph 2) * Cardinal.ord (aleph 2) ∧
      G.chromaticCardinal = ℵ_ 2 ∧
      (∀ (S : Set V),
        Ordinal.type (Subrel (· < ·) S) <
          Cardinal.ord (aleph 2) * Cardinal.ord (aleph 2) →
        (G.induce S).chromaticCardinal ≤ ℵ₀) := by
  sorry

/--
Erdős Problem 919, variant [Er69b]:

What if instead we ask for $G$ to have chromatic number $\aleph_1$?

Is there a graph on a well-ordered set of order type $\omega_2 \cdot \omega_2$ with chromatic
number exactly $\aleph_1$ such that every subgraph induced on a subset of strictly
smaller order type has chromatic number $\leq \aleph_0$?
-/
@[category research open, AMS 3 5]
theorem erdos_919.variants.aleph_1 : answer(sorry) ↔
    ∃ (V : Type) (_ : LinearOrder V) (_ : IsWellOrder V (· < ·))
      (G : SimpleGraph V),
      Ordinal.type ((· < ·) : V → V → Prop) =
        Cardinal.ord (aleph 2) * Cardinal.ord (aleph 2) ∧
      G.chromaticCardinal = ℵ_ 1 ∧
      (∀ (S : Set V),
        Ordinal.type (Subrel (· < ·) S) <
          Cardinal.ord (aleph 2) * Cardinal.ord (aleph 2) →
        (G.induce S).chromaticCardinal ≤ ℵ₀) := by
  sorry

end Erdos919
