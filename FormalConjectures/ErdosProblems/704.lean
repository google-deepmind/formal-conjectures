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
# Erdős Problem 704

*Reference:* [erdosproblems.com/704](https://www.erdosproblems.com/704)

Let $G_n$ be the unit distance graph in $\mathbb{R}^n$, with two vertices joined by an edge
if and only if the Euclidean distance between them is $1$.

Estimate the chromatic number $\chi(G_n)$. Does it grow exponentially in $n$? Does
$\lim_{n \to \infty} \chi(G_n)^{1/n}$ exist?

A generalisation of the Hadwiger–Nelson problem (which addresses $n = 2$).

**Known results:**
- Frankl–Wilson [FrWi81]: $\chi(G_n) \geq (1+o(1)) \cdot 1.2^n$
- Larman–Rogers [LaRo72]: $\chi(G_n) \leq (3+o(1))^n$

[FrWi81] Frankl, P. and Wilson, R. M., _Intersection theorems with geometric consequences_.
Combinatorica 1 (1981), 357–368.

[LaRo72] Larman, D. G. and Rogers, C. A., _The realization of distances within sets in
Euclidean space_. Mathematika 19 (1972), 1–24.
-/

open Filter

open scoped Topology

namespace Erdos704

/-- The unit distance graph in $\mathbb{R}^n$: two points are adjacent iff their
Euclidean distance is exactly $1$. -/
noncomputable def unitDistanceGraph (n : ℕ) : SimpleGraph (EuclideanSpace ℝ (Fin n)) where
  Adj x y := x ≠ y ∧ dist x y = 1
  symm := fun _ _ ⟨hne, hd⟩ => ⟨hne.symm, by rw [dist_comm]; exact hd⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/-- The chromatic number of the unit distance graph in $\mathbb{R}^n$: the minimum number
of colors needed to properly color all points so that no two points at
distance $1$ share the same color. Returns $0$ if no finite coloring exists. -/
noncomputable def chromaticNumber_unitDist (n : ℕ) : ℕ :=
  sInf {k : ℕ | (unitDistanceGraph n).Colorable k}

/--
Erdős Problem 704, main open question:

Does the limit $\lim_{n \to \infty} \chi(G_n)^{1/n}$ exist?
-/
@[category research open, AMS 5 52]
theorem erdos_704 : answer(sorry) ↔
    ∃ L : ℝ, Tendsto
      (fun n : ℕ => (chromaticNumber_unitDist n : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
      atTop (nhds L) := by
  sorry

/--
Erdős Problem 704, Frankl–Wilson lower bound [FrWi81]:

The chromatic number of the unit distance graph in $\mathbb{R}^n$ grows at least
exponentially: $\chi(G_n) \geq (1+o(1)) \cdot 1.2^n$.

Formalized as: there exist $C > 0$ and $N_0$ such that for all $n \geq N_0$,
$\chi(G_n) \geq C \cdot (6/5)^n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_704.variants.lower_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (chromaticNumber_unitDist n : ℝ) ≥ C * ((6 : ℝ) / 5) ^ n := by
  sorry

/--
Erdős Problem 704, Larman–Rogers upper bound [LaRo72]:

$\chi(G_n) \leq (3+o(1))^n$.

Formalized as: there exist $C > 0$ and $N_0$ such that for all $n \geq N_0$,
$\chi(G_n) \leq C \cdot 3^n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_704.variants.upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (chromaticNumber_unitDist n : ℝ) ≤ C * (3 : ℝ) ^ n := by
  sorry

end Erdos704
