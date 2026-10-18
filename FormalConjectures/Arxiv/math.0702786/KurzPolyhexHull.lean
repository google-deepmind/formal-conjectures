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
# Kurz's conjecture on the convex hull of a polyhex

A polyhex is an edge-to-edge connected system of regular hexagons. Kurz conjectured that the
convex hull of a polyhex with $n$ cells of unit area has area at most
$\frac{1}{6}\lfloor n^2 + \frac{14}{3}n + 1 \rfloor$.

*References:*
- [Ku08] [arxiv/math.0702786](https://arxiv.org/abs/math/0702786)
  **Convex hulls of polyominoes**
  by *Sascha Kurz*, Beitr. Algebra Geom. 49 (2008), Conjecture 2.
- [Ga26] [arxiv/2609.30310](https://arxiv.org/abs/2609.30310)
  **The maximum area of the convex hull of a polyhex**
  by *Pragyaan Gaur*.
- [OEIS A399934](https://oeis.org/A399934)
-/

@[expose] public section

open MeasureTheory Set
open scoped Pointwise

namespace Arxiv.«math.0702786»

/-- The six neighbour steps of the hexagonal tiling in axial coordinates. -/
def hexSteps : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}

/-- Two cells of the hexagonal tiling, in axial coordinates, are adjacent when they share an
edge. -/
def hexGraph : SimpleGraph (ℤ × ℤ) where
  Adj x y := y - x ∈ hexSteps
  symm := ⟨fun x y (h : y - x ∈ hexSteps) ↦ by
    show x - y ∈ hexSteps
    rw [← neg_sub]
    simp only [hexSteps, Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h | h | h | h <;> rw [h] <;> decide⟩
  loopless := ⟨fun x (h : x - x ∈ hexSteps) ↦ by
    rw [sub_self] at h
    exact absurd h (by decide)⟩

instance : DecidableRel hexGraph.Adj :=
  fun x y ↦ inferInstanceAs (Decidable (y - x ∈ hexSteps))

/-- A polyhex is a finite, nonempty, edge-connected set of cells. -/
def IsPolyhex (S : Finset (ℤ × ℤ)) : Prop :=
  S.Nonempty ∧ (hexGraph.induce (S : Set (ℤ × ℤ))).Connected

/-- The centre of the cell with axial coordinates `c` in the Euclidean plane. Adjacent centres
are at distance $1$. -/
noncomputable def center (c : ℤ × ℤ) : ℝ × ℝ :=
  ((c.1 : ℝ) + (c.2 : ℝ) / 2, √3 / 2 * c.2)

/-- The regular hexagon centred at the origin whose opposite edges are at distance $1$. -/
noncomputable def hexagon : Set (ℝ × ℝ) :=
  convexHull ℝ {(1 / 2, √3 / 6), (0, √3 / 3), (-1 / 2, √3 / 6),
    (-1 / 2, -√3 / 6), (0, -√3 / 3), (1 / 2, -√3 / 6)}

/-- The union of the cells of `S`. -/
noncomputable def region (S : Finset (ℤ × ℤ)) : Set (ℝ × ℝ) :=
  ⋃ c ∈ S, center c +ᵥ hexagon

@[category test, AMS 52]
theorem hexGraph_adj_one_zero : hexGraph.Adj (0, 0) (1, 0) := by
  decide

@[category test, AMS 52]
theorem not_hexGraph_adj_one_one : ¬ hexGraph.Adj (0, 0) (1, 1) := by
  decide

@[category test, AMS 52]
theorem volume_hexagon : volume hexagon = ENNReal.ofReal (√3 / 2) := by
  sorry

/--
The area of the convex hull of any edge-to-edge connected system of $n$ regular hexagons of unit
area is at most $\frac{1}{6}\lfloor n^2 + \frac{14}{3}n + 1 \rfloor$.

Areas are measured in units of the area of one cell. Gaur [Ga26] proved the conjecture, with a
Lean proof of the upper bound.
-/
@[category research solved, AMS 5 52, formal_proof using lean4 at
  "https://github.com/pragyaangaur/Polyhex-Hull/blob/c8f4dae12aa830aea9fe995ee9cdb15e16a2ac35/PolyhexHull/Euclidean.lean#L107"]
theorem kurz_conjecture (S : Finset (ℤ × ℤ)) (hS : IsPolyhex S) :
    volume.real (convexHull ℝ (region S)) ≤
      volume.real hexagon * (⌊(S.card : ℝ) ^ 2 + 14 / 3 * S.card + 1⌋ / 6) := by
  sorry

/--
The sharp upper bound: the convex hull of a polyhex with $n$ cells of unit area has area at most
$\frac{1}{6}\lceil n^2 + \frac{14}{3}n \rceil$. This differs from Kurz's bound by $\frac{1}{6}$
when $3 \mid n$ and agrees with it otherwise.
-/
@[category research solved, AMS 5 52, formal_proof using lean4 at
  "https://github.com/pragyaangaur/Polyhex-Hull/blob/c8f4dae12aa830aea9fe995ee9cdb15e16a2ac35/PolyhexHull/Main.lean#L197"]
theorem kurz_conjecture.variants.sharp (S : Finset (ℤ × ℤ)) (hS : IsPolyhex S) :
    volume.real (convexHull ℝ (region S)) ≤
      volume.real hexagon * (⌈(S.card : ℝ) ^ 2 + 14 / 3 * S.card⌉ / 6) := by
  sorry

/--
The sharp bound is attained: for every $n \ge 1$ there is a polyhex with $n$ cells whose convex
hull has area $\frac{1}{6}\lceil n^2 + \frac{14}{3}n \rceil$ in units of one cell. A path made of
three straight runs of almost equal length attains it [Ga26].
-/
@[category research solved, AMS 5 52]
theorem kurz_conjecture.variants.attained (n : ℕ) (hn : 1 ≤ n) :
    ∃ S : Finset (ℤ × ℤ), IsPolyhex S ∧ S.card = n ∧
      volume.real (convexHull ℝ (region S)) =
        volume.real hexagon * (⌈(n : ℝ) ^ 2 + 14 / 3 * n⌉ / 6) := by
  sorry

end Arxiv.«math.0702786»
