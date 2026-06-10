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
# Erdős Problem 597

*Reference:* [erdosproblems.com/597](https://www.erdosproblems.com/597)

*References:*
- [Er87] Erdős, P., *Some problems on finite and infinite graphs*. Logic and combinatorics
  (Arcata, Calif., 1985) (1987), 223-228.
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999), problem 7.84.
-/

open Cardinal Ordinal
open scoped Cardinal Ordinal

namespace Erdos597

/--
The graph-target ordinal partition relation $\alpha \to (\beta, G)^2$: for every red/blue
colouring of the edges of the complete graph on $\alpha$, either there is a red clique of
order type $\beta$, or there is a blue copy of the graph $G$ (an injective map sending the
edges of $G$ to blue edges).

This generalises `OrdinalCardinalRamsey`, replacing the blue clique of cardinality $c$
(i.e. a blue copy of $K_c$) by a blue copy of an arbitrary graph $G$.

Will be moved to `FormalConjecturesForMathlib/SetTheory/Ordinal/PartitionRelation.lean`
once the shared home for ordinal partition relations lands (see PR #4195).
-/
def OrdinalGraphRamsey {W : Type*} (α β : Ordinal.{0}) (G : SimpleGraph W) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
    (∃ f : W → α.ToType, Function.Injective f ∧
      ∀ a b, G.Adj a b → blue.Adj (f a) (f b))

/--
**Erdős Problem 597** [Er87] [Va99, 7.84]. Let $G$ be a graph on at most $\aleph_1$
vertices which contains no $K_4$ and no $K_{\aleph_0,\aleph_0}$ (the complete bipartite
graph with $\aleph_0$ vertices in each class). Is it true that
$$\omega_1^2 \to (\omega_1 \omega, G)^2?$$
-/
@[category research open, AMS 3 5]
theorem erdos_597 : answer(sorry) ↔
    ∀ (W : Type) (G : SimpleGraph W), #W ≤ ℵ_ 1 → G.CliqueFree 4 →
      (¬ ∃ A B : Set W, Disjoint A B ∧ A.Infinite ∧ B.Infinite ∧
        ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) →
      OrdinalGraphRamsey ((ω_ 1) ^ (2 : ℕ)) ((ω_ 1) * ω) G := by
  sorry

/--
**Erdős Problem 597, finite case** [Er87] [Va99, 7.84]. Is it true that
$\omega_1^2 \to (\omega_1 \omega, G)^2$ for every finite $K_4$-free graph $G$?
(A finite graph contains no $K_{\aleph_0,\aleph_0}$, so that hypothesis is vacuous.)
-/
@[category research open, AMS 3 5]
theorem erdos_597.variants.finite : answer(sorry) ↔
    ∀ (W : Type) [Fintype W] (G : SimpleGraph W), G.CliqueFree 4 →
      OrdinalGraphRamsey ((ω_ 1) ^ (2 : ℕ)) ((ω_ 1) * ω) G := by
  sorry

/--
Erdős and Hajnal proved that $\omega_1^2 \to (\omega_1 \omega, 3)^2$: in every red/blue
colouring of the edges of the complete graph on $\omega_1^2$ there is either a red clique
of order type $\omega_1 \cdot \omega$ or a blue triangle.
-/
@[category research solved, AMS 3 5]
theorem erdos_597.variants.erdos_hajnal :
    OrdinalCardinalRamsey ((ω_ 1) ^ (2 : ℕ)) ((ω_ 1) * ω) 3 := by
  sorry

/--
Erdős originally asked Problem 597 with just the assumption that $G$ is $K_4$-free, but
Baumgartner proved that $\omega_1^2 \not\to (\omega_1 \omega, K_{\aleph_0,\aleph_0})^2$.
-/
@[category research solved, AMS 3 5]
theorem erdos_597.variants.baumgartner :
    ¬ OrdinalGraphRamsey ((ω_ 1) ^ (2 : ℕ)) ((ω_ 1) * ω) (completeBipartiteGraph ℕ ℕ) := by
  sorry

/--
Sanity check: the relation $\omega_1^2 \to (\omega_1 \omega, G)^2$ holds trivially when
$G$ is a single vertex with no edges, since any vertex of $\omega_1^2$ is a blue copy
of $G$.
-/
@[category test, AMS 3]
theorem ordinalGraphRamsey_bot :
    OrdinalGraphRamsey ((ω_ 1) ^ (2 : ℕ)) ((ω_ 1) * ω) (⊥ : SimpleGraph (Fin 1)) := by
  intro red blue _
  right
  have : Nonempty ((ω_ 1) ^ (2 : ℕ)).ToType := by
    rw [Ordinal.toType_nonempty_iff_ne_zero]
    exact pow_ne_zero 2 (omega_pos 1).ne'
  obtain ⟨x⟩ := this
  exact ⟨fun _ => x, fun a b _ => Subsingleton.elim a b, fun a b h => by simp at h⟩

end Erdos597
