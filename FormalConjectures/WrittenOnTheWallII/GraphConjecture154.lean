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
# Written on the Wall II - Conjecture 154

*References:*
- [E. DeLaViña, Written on the Wall II, Conjectures of Graffiti.pc](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf), entry 154 (August 8, 2005).
- [takumayellow/math-autoresearch, Lower bounds for the spanning-tree leaf number (p0010)](https://github.com/takumayellow/math-autoresearch/tree/c24c95c4e0f706f5e236ad6b5bd68ca9a851710c/papers/p0010_wowii_ls_lower_bounds).

For a finite nontrivial connected simple graph $G$ of radius $r = \mathrm{rad}(G)$, let
$C(G) = \{v \mid \mathrm{ecc}(v) = r\}$ be the center of $G$, and for $v \in C(G)$ let
$R(v) = \{w \mid \mathrm{dist}_G(v, w) = r\}$ be its radial circle. Conjecture 154 proposed that
the maximum number $L_s(G)$ of leaves in a spanning tree satisfies
$$L_s(G) \ge \frac{1 + \max_{v \in C(G)} |R(v)|}{\min_{v \in C(G)} |R(v)|}.$$

The conjecture is **false**: there is a $15$-vertex connected graph of radius $3$ whose seven
center vertices have radial-circle orders $\{1, 4, 5, 6, 8\}$ ($\max |R(v)| = 8$ and
$\min |R(v)| = 1$, giving a proposed bound of $(1 + 8) / 1 = 9$), while three internally disjoint
paths between two branch vertices force $L_s(G) = 8$.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture154

open SimpleGraph

/-- The center $C(G)$ of a finite graph: the vertices whose eccentricity equals the radius. -/
noncomputable def centerFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Finset V :=
  open scoped Classical in
  Finset.univ.filter fun v => G.eccent v = G.radius

/-- The radial circle $R(v)$ of a vertex $v$: the vertices at distance $\mathrm{rad}(G)$ from $v$. -/
noncomputable def radialCircle {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : Finset V :=
  open scoped Classical in
  Finset.univ.filter fun w => G.dist v w = G.radius.toNat

/-- The set of radial-circle orders $\{|R(v)| \mid v \in C(G)\}$ over all center vertices. -/
noncomputable def radialCircleOrders {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Finset ℕ :=
  open scoped Classical in
  (centerFinset G).image fun v => (radialCircle G v).card

/-- Every nonempty finite graph has at least one center vertex, so `radialCircleOrders G` is nonempty. -/
@[category API, AMS 5]
theorem radialCircleOrders_nonempty {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : (radialCircleOrders G).Nonempty := by
  classical
  obtain ⟨u, hu⟩ := G.exists_eccent_eq_radius
  exact ⟨(radialCircle G u).card,
    Finset.mem_image.mpr ⟨u, by simpa [centerFinset] using hu, rfl⟩⟩

/--
WOWII [Conjecture 154](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf):
does every finite nontrivial connected simple graph $G$ satisfy
$L_s(G) \ge (1 + \max_{v \in C(G)} |R(v)|) / \min_{v \in C(G)} |R(v)|$,
where $C(G)$ is the center of $G$ and $R(v)$ is the radial circle of $v$?

This is false: a $15$-vertex connected graph of radius $3$ attains radial-circle orders
$\{1, 4, 5, 6, 8\}$ over its centers and has $L_s(G) = 8 < (1 + 8) / 1 = 9$.
The linked Palomar proof certifies the equivalent cross-multiplied inequality on this graph.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-28-000012"]
theorem conjecture154 :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
        ((1 + (radialCircleOrders G).max' (radialCircleOrders_nonempty G) : ℕ) : ℝ) /
          ((radialCircleOrders G).min' (radialCircleOrders_nonempty G) : ℝ) ≤ Ls G := by
  sorry

-- Sanity checks

/-- Every nonempty finite graph has at least one central radial-circle order. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 1 ≤ (radialCircleOrders G).card :=
  Finset.one_le_card.mpr (radialCircleOrders_nonempty G)

/-- Each radial circle has cardinality at most $|V|$. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) (v : Fin 4) : (radialCircle G v).card ≤ 4 :=
  (Finset.card_le_univ _).trans (by simp)

end WrittenOnTheWallII.GraphConjecture154
