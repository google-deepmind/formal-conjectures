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
# Erdős Problem 1086

*References:*
- [erdosproblems.com/1086](https://www.erdosproblems.com/1086)
- [ErPu71] Erdős, Paul and Purdy, George, *Some extremal problems in geometry*. J. Combinatorial
  Theory Ser. A (1971), 246--252.
- [RaSh17] Raz, Orit E. and Sharir, Micha, *The number of unit-area triangles in the plane: theme
  and variation*. Combinatorica (2017), 1221--1240.
-/

open Filter Real
open scoped EuclideanGeometry Asymptotics

namespace Erdos1086

/--
A finite point set determines a triangle of unsigned area `a`.
-/
def HasUnsignedArea (a : ℝ) (T : Finset ℝ²) : Prop :=
  ∃ x y z, T = {x, y, z} ∧ |EuclideanGeometry.triangle_area x y z| = a

/-- The number of triangles of unsigned area `a` determined by a finite point set in the plane. -/
noncomputable def triangleNumOfArea (P : Finset ℝ²) (a : ℝ) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter (HasUnsignedArea a)).card

/--
$g(n)$ is the least number such that every set of $n$ points in $\mathbb{R}^2$ contains the
vertices of at most $g(n)$ triangles of equal positive area.

The positivity restriction excludes collinear triples, which all have area $0$. Equivalently,
$g(n)$ is the maximal number of unit-area triangles determined by an $n$-point set in the plane.
-/
noncomputable def g (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ P : Finset ℝ², P.card = n → ∀ a : ℝ, 0 < a → triangleNumOfArea P a ≤ m}

@[category test, AMS 52]
theorem triangleNumOfArea_empty (a : ℝ) :
    triangleNumOfArea (∅ : Finset ℝ²) a = 0 := by
  simp [triangleNumOfArea, HasUnsignedArea]

@[category test, AMS 52]
theorem triangleNumOfArea_eq_zero_of_card_lt_three {P : Finset ℝ²} {a : ℝ} (hP : P.card < 3) :
    triangleNumOfArea P a = 0 := by
  simp [triangleNumOfArea, Finset.powersetCard_eq_empty.2 hP]

@[category test, AMS 52]
theorem g_eq_zero_of_lt_three {n : ℕ} (hn : n < 3) : g n = 0 := by
  refine Nat.eq_zero_of_le_zero (csInf_le (OrderBot.bddBelow _) ?_)
  intro P hP _a _ha
  exact (triangleNumOfArea_eq_zero_of_card_lt_three (hP ▸ hn)).le

/--
Let $g(n)$ be minimal such that any set of $n$ points in $\mathbb{R}^2$ contains the vertices of
at most $g(n)$ many triangles with the same area. Estimate $g(n)$.
-/
@[category research open, AMS 52]
theorem erdos_1086 :
    (fun n : ℕ => (g n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Erdős and Purdy [ErPu71] proved $n^2\log\log n \ll g(n)$. -/
@[category research solved, AMS 52]
theorem erdos_1086.variants.lower_bound :
    (fun n : ℕ => (n : ℝ) ^ 2 * log (log n)) ≪ fun n : ℕ => (g n : ℝ) := by
  sorry

/-- Erdős and Purdy [ErPu71] proved $g(n) \ll n^{5/2}$. -/
@[category research solved, AMS 52]
theorem erdos_1086.variants.upper_bound :
    (fun n : ℕ => (g n : ℝ)) ≪ fun n : ℕ => (n : ℝ) ^ (5 / 2 : ℝ) := by
  sorry

/-- Raz and Sharir [RaSh17] proved $g(n) \ll n^{20/9}$. -/
@[category research solved, AMS 52]
theorem erdos_1086.variants.upper_bound_raz_sharir :
    (fun n : ℕ => (g n : ℝ)) ≪ fun n : ℕ => (n : ℝ) ^ (20 / 9 : ℝ) := by
  sorry

end Erdos1086
