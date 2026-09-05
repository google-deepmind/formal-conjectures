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
# The Neumann-Lara conjecture on the dichromatic number of planar digraphs

The *dichromatic number* of a digraph `D` is the least number of colours needed
to colour its vertices so that each colour class induces an *acyclic* subdigraph
(no directed cycle). This is the directed analogue of the chromatic number.

The *digirth* of a digraph is the length of a shortest directed cycle. Digirth
`≥ 3` rules out loops and 2-cycles (pairs of anti-parallel arcs), i.e. it means
the digraph is an *oriented* graph (an orientation of a simple graph).

Neumann-Lara (1985), and independently Škrekovski, conjectured that every planar
oriented graph is 2-dicolourable:

> **Conjecture.** Every planar digraph of digirth at least `3` has dichromatic
> number at most `2`.

Mathlib has no `Digraph` type carrying a dichromatic number, no graph minors, and
no planarity predicate, so we build everything from scratch. A digraph on a vertex
type `V` is modelled as an irreflexive relation `Adj : V → V → Prop` (an arc from
`a` to `b`). A directed cycle of length `k ≥ 1` is an injective `c : Fin k → V`
with an arc from `c i` to `c (i + 1)` cyclically.

Since Mathlib lacks planarity we define it combinatorially via **Wagner's
theorem**: a finite graph is planar iff it has neither `K₅` nor `K₃,₃` as a minor.
We spell out a self-contained minor notion (disjoint connected branch sets, one per
vertex of the model, with an edge between adjacent branch sets) and use it both for
`K₅`/`K₃,₃`-freeness (planarity) and for Steiner's `K₅`-minor-free reformulation.

*References:*
- [Wikipedia: Dichromatic number](https://en.wikipedia.org/wiki/Dichromatic_number)
- V. Neumann-Lara, *The dichromatic number of a digraph*, J. Combin. Theory Ser.
  B 33 (1982), 265–270. (Origin of the dichromatic number; the planar conjecture
  is attributed to Neumann-Lara 1985 and independently to Škrekovski.)
- [LM17] Z. Li and B. Mohar, *Planar digraphs of digirth four are 2-colorable*,
  SIAM J. Discrete Math. 31 (2017), 2201–2205.
  [doi:10.1137/16M108080X](https://doi.org/10.1137/16M108080X), arXiv:1606.06114.
- [St19] R. Steiner, *A note on graphs of dichromatic number 2*, Discrete Math.
  Theor. Comput. Sci. 21 (2019), #4. arXiv:1907.00351.
  <https://dmtcs.episciences.org/7040>
- P. Knauer and P. Valicov verified the conjecture for all planar digraphs on at
  most `26` vertices.
-/

open scoped Finset
open SimpleGraph

namespace NeumannLara

/-! ### Digraphs, directed cycles, digirth, and the dichromatic number -/

variable {V : Type*}

/-- A *digraph* on a vertex type `V`: an irreflexive relation `Adj`, where
`Adj a b` means there is an arc from `a` to `b`. Irreflexivity forbids loops. -/
structure Digraph (V : Type*) where
  /-- `Adj a b` holds when there is an arc from `a` to `b`. -/
  Adj : V → V → Prop
  /-- There are no loops. -/
  irrefl : ∀ a, ¬ Adj a a

/-- A *directed cycle* of length `k` in `D`: an injective tour
`c : Fin k → V` with an arc from `c i` to the cyclically next vertex `c (i + 1)`.
We require `k ≥ 1`; note `Fin k` addition is modular, so for `k = 1` this would
demand a loop (excluded by irreflexivity) and for `k = 2` a pair of anti-parallel
arcs. -/
def IsDirectedCycleOfLength (D : Digraph V) (k : ℕ) (c : Fin k → V) : Prop :=
  1 ≤ k ∧ Function.Injective c ∧ ∀ i : Fin k, D.Adj (c i) (c (i + 1))

/-- `D` *has a directed cycle* if it has a directed cycle of some length `k ≥ 1`. -/
def HasDirectedCycle (D : Digraph V) : Prop :=
  ∃ (k : ℕ) (c : Fin k → V), IsDirectedCycleOfLength D k c

/-- `D` has *digirth at least `g`*: every directed cycle has length at least `g`.
Equivalently, there is no directed cycle of length in `[1, g - 1]`. -/
def DigirthGE (D : Digraph V) (g : ℕ) : Prop :=
  ∀ (k : ℕ) (c : Fin k → V), IsDirectedCycleOfLength D k c → g ≤ k

/-- The digraph induced by `D` on a vertex subset `S`: same arcs, restricted to
`S`. Modelled on the subtype `↥S`. -/
def induced (D : Digraph V) (S : Set V) : Digraph S where
  Adj a b := D.Adj a b
  irrefl a := D.irrefl a

/-- A vertex subset `S` induces an *acyclic* subdigraph if the digraph `D`
restricted to `S` has no directed cycle. -/
def InducesAcyclic (D : Digraph V) (S : Set V) : Prop :=
  ¬ HasDirectedCycle (D.induced S)

/-- `D` is *`k`-dicolourable* (`DichromaticLE D k`): there is a colouring
`col : V → Fin k` such that each colour class `{v | col v = c}` induces an acyclic
subdigraph. The *dichromatic number* is the least such `k`. -/
def DichromaticLE (D : Digraph V) (k : ℕ) : Prop :=
  ∃ col : V → Fin k, ∀ c : Fin k, InducesAcyclic D {v | col v = c}

/-! ### Underlying graph and planarity

Planarity is not in Mathlib; we use the combinatorial (Wagner) predicate
`SimpleGraph.IsPlanar` from
`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Planar` (no `K₅` and no
`K₃,₃` minor), built on `SimpleGraph.IsMinor`. -/

/-- The *underlying simple graph* of a digraph `D`: an (undirected) edge between
`a` and `b` whenever there is an arc in either direction and `a ≠ b`. -/
def underlying (D : Digraph V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (D.Adj a b ∨ D.Adj b a)
  symm := by
    rintro a b ⟨hab, h⟩
    exact ⟨hab.symm, h.symm⟩
  loopless := by
    rintro a ⟨h, -⟩
    exact h rfl

/-- A digraph is *planar* if its underlying simple graph is planar (in the
combinatorial Wagner sense above). -/
def IsPlanarDigraph (D : Digraph V) : Prop :=
  IsPlanar D.underlying

/-! ### The conjecture -/

/--
**The Neumann-Lara conjecture (1985; independently Škrekovski).**
Every planar digraph of digirth at least `3` has dichromatic number at most `2`.

We quantify over all finite vertex counts `n` and digraphs on `Fin n`.
-/
@[category research open, AMS 5]
theorem neumann_lara :
    ∀ (n : ℕ) (D : Digraph (Fin n)),
      IsPlanarDigraph D → DigirthGE D 3 → DichromaticLE D 2 := by
  sorry

namespace variants

/--
**[LM17] Li–Mohar.** Every planar digraph of digirth at least `4` is
2-dicolourable. This is the best digirth bound known towards the conjecture
(which asks for digirth `≥ 3`).
-/
@[category research solved, AMS 5]
theorem li_mohar_digirth_four :
    ∀ (n : ℕ) (D : Digraph (Fin n)),
      IsPlanarDigraph D → DigirthGE D 4 → DichromaticLE D 2 := by
  sorry

/--
**Knauer–Valicov.** The Neumann-Lara conjecture holds for all planar digraphs on
at most `26` vertices: every such digraph of digirth at least `3` is
2-dicolourable.
-/
@[category research solved, AMS 5]
theorem knauer_valicov_small :
    ∀ (n : ℕ), n ≤ 26 → ∀ (D : Digraph (Fin n)),
      IsPlanarDigraph D → DigirthGE D 3 → DichromaticLE D 2 := by
  sorry

/-- The digraph obtained by *orienting* a simple graph `G` according to a relation
`R` (keep the arc `a → b` when `R a b` holds and `G.Adj a b`). We only assert the
relevant properties abstractly through `IsOrientationOf` below. -/
def IsOrientationOf (D : Digraph V) (G : SimpleGraph V) : Prop :=
  (∀ a b, D.Adj a b → G.Adj a b) ∧
  (∀ a b, G.Adj a b → (D.Adj a b ↔ ¬ D.Adj b a)) ∧
  DigirthGE D 3

/--
**[St19] Steiner's equivalence.** The Neumann-Lara conjecture is *equivalent* to:
every orientation of every `K₅`-minor-free (finite) graph is 2-dicolourable.

Both sides are quantified over all finite vertex counts. The right-hand side
speaks about orientations `D` of a `K₅`-minor-free simple graph `G`.
-/
@[category research solved, AMS 5]
theorem steiner_equivalence :
    (∀ (n : ℕ) (D : Digraph (Fin n)),
        IsPlanarDigraph D → DigirthGE D 3 → DichromaticLE D 2)
      ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (D : Digraph (Fin n)),
        ¬ HasKMinor G 5 → IsOrientationOf D G → DichromaticLE D 2) := by
  sorry

end variants

end NeumannLara
