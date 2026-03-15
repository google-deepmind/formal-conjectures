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

Erdős asked whether the ordinal partition relation ω₁² → (ω₁·ω, G)² holds for
every graph G on at most ℵ₁ vertices that is K₄-free and contains no K_{ℵ₀,ℵ₀}.

*Reference:* [erdosproblems.com/597](https://www.erdosproblems.com/597)

[Er87] Erdős, P., _Some problems on finite and infinite graphs_, Logic and combinatorics,
Contemp. Math. **65** (1987), 223–228.

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
"Paul Erdős and his mathematics", Budapest, July 1999, §7.84.
-/

open Cardinal SimpleGraph

namespace Erdos597

/-- The type of ordinals strictly less than $\alpha$. -/
abbrev OrdinalSet (α : Ordinal) := {a : Ordinal // a < α}

/-- A graph $G$ contains a complete bipartite subgraph $K_{\kappa,\kappa}$ if there exist
disjoint vertex sets $A$ and $B$, each of cardinality at least $\kappa$,
such that every vertex in $A$ is adjacent to every vertex in $B$. -/
def ContainsBiclique {V : Type*} (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∃ (A B : Set V), Disjoint A B ∧ #A ≥ κ ∧ #B ≥ κ ∧
    ∀ a ∈ A, ∀ b ∈ B, G.Adj a b

/-- The ordinal-graph partition relation $\alpha \to (\beta, G)^2$:
every $2$-coloring of ordered pairs from `OrdinalSet α` yields either:
- an order-embedded copy of $\beta$ whose pairs are all colored $0$, or
- a copy of $G$ in the color-$1$ graph (an injective map preserving edges).

Here a "copy of $\beta$" is given by an order embedding
$e : \operatorname{OrdinalSet}(\beta) \hookrightarrow \operatorname{OrdinalSet}(\alpha)$,
and monochromaticity means $f(e(i), e(j)) = 0$ for all $i < j$. A "copy of $G$"
is an injective map $g : V \to \operatorname{OrdinalSet}(\alpha)$ such that every edge of $G$
maps to a pair colored $1$.

Note: the coloring `f` is not required to be symmetric — only the "upper triangle"
(pairs with `i < j`) is consulted. -/
def OrdGraphPartition (α β : Ordinal) {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (f : OrdinalSet α → OrdinalSet α → Fin 2),
    (∃ e : OrdinalSet β ↪o OrdinalSet α,
      ∀ i j : OrdinalSet β, i < j → f (e i) (e j) = 0) ∨
    (∃ g : V → OrdinalSet α, Function.Injective g ∧
      ∀ u v : V, G.Adj u v → g u < g v → f (g u) (g v) = 1)

/--
Erdős Problem 597 [Er87] [Va99, 7.84]:

If $G$ is a graph on at most $\aleph_1$ vertices containing no $K_4$ and no
$K_{\aleph_0,\aleph_0}$, is it true that
$$\omega_1^2 \to (\omega_1 \cdot \omega, G)^2?$$

Erdős and Hajnal proved that $\omega_1^2 \to (\omega_1 \cdot \omega, 3)^2$. Erdős originally
asked this with just the assumption that $G$ is $K_4$-free, but Baumgartner proved that
$\omega_1^2 \not\to (\omega_1 \cdot \omega, K_{\aleph_0,\aleph_0})^2$.
-/
@[category research open, AMS 3 5]
theorem erdos_597 : answer(sorry) ↔
    ∀ (V : Type*) (G : SimpleGraph V),
      #V ≤ aleph 1 → G.CliqueFree 4 → ¬ContainsBiclique G (aleph 0) →
      OrdGraphPartition ((aleph 1).ord ^ 2) ((aleph 1).ord * (aleph 0).ord) G := by
  sorry

end Erdos597
