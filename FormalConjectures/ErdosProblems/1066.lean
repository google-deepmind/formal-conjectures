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
# Erdős Problem 1066

*References:*
- [erdosproblems.com/1066](https://www.erdosproblems.com/1066)
- [Cs98] Csizmadia, G., *On the independence number of minimum distance graphs*. Discrete Comput.
  Geom. (1998), 179--187.
- [PaTo96] Pach, János and Tóth, Géza, *On the independence number of coin graphs*. Geombinatorics
  (1996), 30--33.
- [Po85] Pollack, R., *Increasing the minimum distance of a set of points*. J. Combin. Theory Ser. A
  (1985), 450.
- [Sw02] Swanepoel, Konrad J., *Independence numbers of planar contact graphs*. Discrete Comput.
  Geom. (2002), 649--670.
-/

open Filter Metric SimpleGraph
open scoped Asymptotics EuclideanGeometry Topology

namespace Erdos1066

/--
`g n` is maximal such that every unit distance graph on `n` points in $\mathbb{R}^2$ with
minimum distance $1$ has an independent set of size at least `g n`.
-/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k | ∀ V : Finset ℝ², V.card = n → IsSeparated' 1 (V : Set ℝ²) →
    k ≤ (UnitDistancePlaneGraph (V : Set ℝ²)).indepNum}

/--
Let $G$ be a graph given by $n$ points in $\mathbb{R}^2$, where any two distinct points are at
least distance $1$ apart, and we draw an edge between two points if they are distance $1$ apart.

Let $g(n)$ be maximal such that any such graph always has an independent set on at least $g(n)$
vertices. Estimate $g(n)$, or perhaps $\lim \frac{g(n)}{n}$.

Such graphs are always planar. Erdős initially thought that $g(n)=n/3$, but Chung and Graham, and
independently Pach, gave a construction that shows $g(n)\leq \frac{6}{19}n$. Pach and Toth
[PaTo96] improved this to $g(n)\leq \frac{5}{16}n$.

Pollack [Po85] noted that the Four colour theorem implies $g(n)\geq n/4$, since the graph is
planar. This lower bound has been improved to $\frac{9}{35}n$ by Csizmadia [Cs98] and then
$\frac{8}{31}n$ by Swanepoel [Sw02]. The current record bounds are therefore
$$\frac{8}{31}n \approx 0.258n \leq g(n) \leq 0.3125n=\frac{5}{16}n.$$
-/
@[category research open, AMS 52]
theorem erdos_1066 :
    Tendsto (fun n : ℕ ↦ (g n : ℝ) / n) atTop (𝓝 (answer(sorry) : ℝ)) := by
  sorry

/--
Pollack [Po85] noted that the Four colour theorem implies $g(n)\geq n/4$, since such graphs are
planar.
-/
@[category research solved, AMS 52]
theorem erdos_1066.variants.pollack (n : ℕ) : (n : ℝ) / 4 ≤ g n := by
  sorry

/--
Pach and Toth [PaTo96] proved $g(n)\leq \frac{5}{16}n$.
-/
@[category research solved, AMS 52]
theorem erdos_1066.variants.pach_toth : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (5 / 16) * n := by
  sorry

/--
Swanepoel [Sw02] proved $g(n)\geq \frac{8}{31}n$.
-/
@[category research solved, AMS 52]
theorem erdos_1066.variants.swanepoel : ∀ᶠ n : ℕ in atTop, (8 / 31 : ℝ) * n ≤ g n := by
  sorry

/--
`gDim d n` is maximal such that any set of $n$ points in $\mathbb{R}^d$ with minimum distance $1$
contains at least `gDim d n` points with minimum distance $>1$.
-/
noncomputable def gDim (d n : ℕ) : ℕ :=
  sSup {k | ∀ V : Finset (ℝ^ d), V.card = n → IsSeparated' 1 (V : Set (ℝ^ d)) →
    ∃ S ⊆ V, S.card = k ∧ (S : Set (ℝ^ d)).Pairwise fun x y ↦ 1 < dist x y}

/--
Pollack [Po85] reports a letter from Erdős asking: given $n$ points in $\mathbb{R}^d$ with
minimum distance $1$, let $g_d(n)$ be maximal such that there always exist at least $g_d(n)$ many
points which have minimum distance $>1$. Is it true that $g_d(n) \gg n/d$ in general?
-/
@[category research open, AMS 52]
theorem erdos_1066.variants.higher_dim :
    answer(sorry) ↔ ∀ d : ℕ, 1 ≤ d →
      (fun n : ℕ ↦ (n : ℝ) / d) =O[atTop] fun n ↦ (gDim d n : ℝ) := by
  sorry

/--
The upper bound $g_d(n) \ll n/d$ is trivial, considering widely spaced unit simplices.
-/
@[category research solved, AMS 52]
theorem erdos_1066.variants.higher_dim_upper (d : ℕ) (hd : 1 ≤ d) :
    (fun n ↦ (gDim d n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) / d := by
  sorry

@[category test, AMS 52]
theorem g_zero : g 0 = 0 := by
  sorry

@[category test, AMS 52]
theorem g_one : g 1 = 1 := by
  sorry

@[category test, AMS 52]
theorem g_le_card (n : ℕ) : g n ≤ n := by
  sorry

end Erdos1066
