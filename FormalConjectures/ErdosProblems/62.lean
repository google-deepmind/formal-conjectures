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
# Erdős Problem 62

*References:*
- [erdosproblems.com/62](https://www.erdosproblems.com/62)
- [Er87] Erdős, Paul, *Some problems on finite and infinite graphs*. Logic and combinatorics
  (Arcata, Calif., 1985), Contemp. Math. 65 (1987), 223-228.
- [Er90] Erdős, Paul, *Some of my favourite unsolved problems*. A tribute to Paul Erdős (1990),
  467-478.
- [Er95d] Erdős, Paul, *Some of my favourite problems in various branches of combinatorics*.
  Matematiche (Catania) 47 (1992), no. 2, 231-240 (1995).
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999 (1999), Problem 7.89.
-/

@[expose] public section

open Cardinal SimpleGraph

namespace Erdos62

/--
If $G_1, G_2$ are two graphs with chromatic number $\aleph_1$, must there exist a graph $G$
with chromatic number $4$ which is a subgraph of both $G_1$ and $G_2$?

"Subgraph" means a copy up to isomorphism, expressed by `SimpleGraph.IsContained` (`⊑`).
-/
@[category research open, AMS 3 5]
theorem erdos_62 :
    answer(sorry) ↔
      ∀ (V₁ V₂ : Type) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
        G₁.chromaticCardinal = ℵ_ 1 → G₂.chromaticCardinal = ℵ_ 1 →
          ∃ (W : Type) (G : SimpleGraph W), G.chromaticCardinal = 4 ∧ G ⊑ G₁ ∧ G ⊑ G₂ := by
  sorry

/--
The stronger version: if $G_1, G_2$ are two graphs with chromatic number $\aleph_1$, must
there exist a graph $G$ with chromatic number $\aleph_0$ which is a subgraph of both
$G_1$ and $G_2$?
-/
@[category research open, AMS 3 5]
theorem erdos_62.variants.aleph0 :
    answer(sorry) ↔
      ∀ (V₁ V₂ : Type) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
        G₁.chromaticCardinal = ℵ_ 1 → G₂.chromaticCardinal = ℵ_ 1 →
          ∃ (W : Type) (G : SimpleGraph W), G.chromaticCardinal = ℵ₀ ∧ G ⊑ G₁ ∧ G ⊑ G₂ := by
  sorry

/--
Erdős also asked [Er87]: given finitely many graphs $G_1, \dots, G_n$ with chromatic number
$\aleph_1$, must there be a graph $H$ with chromatic number $4$ or $\aleph_0$ which is a
subgraph of every $G_i$?
-/
@[category research open, AMS 3 5]
theorem erdos_62.variants.finite_collection :
    answer(sorry) ↔
      ∀ (n : ℕ) (V : Fin n → Type) (G : ∀ i, SimpleGraph (V i)),
        (∀ i, (G i).chromaticCardinal = ℵ_ 1) →
          ∃ (W : Type) (H : SimpleGraph W),
            (H.chromaticCardinal = 4 ∨ H.chromaticCardinal = ℵ₀) ∧ ∀ i, H ⊑ G i := by
  sorry

/--
Erdős wrote [Er87] that 'probably' every graph with chromatic number $\aleph_1$ contains as
subgraphs all graphs with chromatic number $4$ with sufficiently large girth.

We state this for finite graphs $H$. The girth bound $g$ may depend on $G$. Since there are
finite graphs with chromatic number $4$ and arbitrarily large girth, a positive answer implies
a positive answer to `erdos_62`.
-/
@[category research open, AMS 3 5]
theorem erdos_62.variants.large_girth :
    answer(sorry) ↔
      ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
        ∃ g : ℕ, ∀ (W : Type) [Finite W] (H : SimpleGraph W),
          H.chromaticCardinal = 4 → g ≤ H.girth → H ⊑ G := by
  sorry

end Erdos62
