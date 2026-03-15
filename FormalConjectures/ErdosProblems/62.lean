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
# Erdős Problem 62

*Reference:* [erdosproblems.com/62](https://www.erdosproblems.com/62)

If $G_1$ and $G_2$ are graphs with chromatic number $\aleph_1$, must they share a common
subgraph with infinite chromatic number?

[EHS74] Erdős, P., Hajnal, A., and Shelah, S., _On some general properties of chromatic numbers_,
Topics in Topology, Colloq. Math. Soc. Janos Bolyai **8** (1974), 243–255.

[Er87] Erdős, P., _Some problems on finite and infinite graphs_, Logic and combinatorics,
Contemp. Math. **65** (1987), 223–228.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
467–478.

[Er95d] Erdős, P., _Problems and results in discrete mathematics_, Discrete Math., 1995.

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
"Paul Erdős and his mathematics", Budapest, July 1999.
-/

open SimpleGraph Cardinal

namespace Erdos62

/-- $G$ contains $H$ as a subgraph via an injective adjacency-preserving map. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Problem 62 (strong version) [Er87]:

If $G_1$, $G_2$ are two graphs with chromatic number $\aleph_1$, must there exist a graph $H$
with infinite chromatic number ($\chi \geq \aleph_0$) which is a subgraph of both $G_1$ and $G_2$?

This is the stronger form of the conjecture. Erdős also asked [Er87] about
finding such a common subgraph in any finite collection of graphs with
chromatic number $\aleph_1$.
-/
@[category research open, AMS 5]
theorem erdos_62 : answer(sorry) ↔
    ∀ (V₁ : Type*) (V₂ : Type*) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    G₁.chromaticCardinal = aleph 1 →
    G₂.chromaticCardinal = aleph 1 →
    ∃ (U : Type*) (H : SimpleGraph U),
      H.chromaticNumber = ⊤ ∧
      ContainsSubgraph G₁ H ∧
      ContainsSubgraph G₂ H := by
  sorry

/--
Erdős Problem 62 (weak version) [Er87]:

If $G_1$, $G_2$ are two graphs with chromatic number $\aleph_1$, must there exist a graph $H$
with chromatic number at least $4$ which is a subgraph of both $G_1$ and $G_2$?

Every graph with chromatic number $\aleph_1$ contains all sufficiently large odd
cycles (chromatic number $3$), proved by Erdős, Hajnal, and Shelah [EHS74].
Erdős wrote [Er87] that 'probably' every graph with chromatic number $\aleph_1$
contains as subgraphs all graphs with chromatic number $4$ with sufficiently
large girth.
-/
@[category research open, AMS 5]
theorem erdos_62.variants.weak : answer(sorry) ↔
    ∀ (V₁ : Type*) (V₂ : Type*) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    G₁.chromaticCardinal = aleph 1 →
    G₂.chromaticCardinal = aleph 1 →
    ∃ (U : Type*) (H : SimpleGraph U),
      ¬ H.Colorable 3 ∧
      ContainsSubgraph G₁ H ∧
      ContainsSubgraph G₂ H := by
  sorry

/--
Erdős Problem 62 (finite collection variant) [Er87]:

If $G_1, \ldots, G_n$ are finitely many graphs each with chromatic number $\aleph_1$, must
there exist a graph $H$ with infinite chromatic number which is a subgraph of every $G_i$?

This is a strictly stronger form of the conjecture, mentioned by Erdős in [Er87].
-/
@[category research open, AMS 5]
theorem erdos_62.variants.finite_collection : answer(sorry) ↔
    ∀ (n : ℕ) (V : Fin n → Type*) (G : ∀ i, SimpleGraph (V i)),
    (∀ i, (G i).chromaticCardinal = aleph 1) →
    ∃ (U : Type*) (H : SimpleGraph U),
      H.chromaticNumber = ⊤ ∧
      ∀ i, ContainsSubgraph (G i) H := by
  sorry

end Erdos62
