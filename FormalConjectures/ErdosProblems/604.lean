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
# Erdős Problem 604

*References:*
- [erdosproblems.com/604](https://www.erdosproblems.com/604)
- [Er46] Erdős, Paul, *On sets of distances of $n$ points*. Amer. Math. Monthly (1946), 248--250.
- [Er57] Erdős, Paul, *Some unsolved problems*. Michigan Math. J. (1957), 291-300.
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Er75f] Erdős, Paul, *On some problems of elementary and combinatorial geometry*. Ann. Mat. Pura
  Appl. (4) (1975), 99-108.
- [Er83c] Erdős, Paul, *Combinatorial problems in geometry*. Math. Chronicle (1983), 35-54.
- [Er85] Erdős, P., *Problems and results in combinatorial geometry*. Discrete geometry and
  convexity (New York, 1982) (1985), 1-11.
- [Er87b] Erdős, P., *Some combinatorial and metric problems in geometry*. Intuitive geometry
  (Siófok, 1985) (1987), 167-177.
- [Er90] Erdős, Paul, *Some of my favourite unsolved problems*. A tribute to Paul Erdős (1990),
  467-478.
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [Er97b] Erdős, Paul, *Some old and new problems in various branches of combinatorics*. Discrete
  Math. (1997), 227-231.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul Erdős,
  I (1997), 47-67.
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [Er97f] Erdős, Paul, *Some unsolved problems*. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
- [KaTa04] Katz, Nets Hawk and Tardos, Gábor, *A new entropy inequality for the Erdős distance
  problem*. Towards a theory of geometric graphs (2004), 119-126.
-/

@[expose] public section

open Filter
open scoped EuclideanGeometry Finset

namespace Erdos604

/-- The pinned distance function $f(n)$. For a set $A$ of $n$ points in $\mathbb{R}^2$, take the
largest number of distinct distances from a point $x \in A$ to the other points of $A$. Then
$f(n)$ is the least such value over all such sets $A$.

The distance $d(x, x) = 0$ is not counted, as in `distinctDistancesFrom`. Every $n$ admits a set
of $n$ points in $\mathbb{R}^2$, so the infimum is a minimum. -/
noncomputable def pinnedDistinctDistances (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A : Finset ℝ², #A = n ∧ A.sup (distinctDistancesFrom A) = m}

/--
Given $n$ distinct points $A\subset\mathbb{R}^2$, must there be a point $x\in A$ such that
$$\#\{ d(x,y) : y \in A\} \gg n^{1-o(1)}?$$

This is the pinned distance problem, a stronger form of Problem 89. Here $n^{1-o(1)}$ means: for
every $\varepsilon > 0$ and all large $n$, the bound is at least $n^{1-\varepsilon}$. We do not
count the distance $d(x, x) = 0$; this changes the count by one.
-/
@[category research open, AMS 52]
theorem erdos_604 : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 - ε) ≤ (pinnedDistinctDistances n : ℝ) := by
  sorry

/--
Given $n$ distinct points $A\subset\mathbb{R}^2$, must there be a point $x\in A$ such that
$$\#\{ d(x,y) : y \in A\} \gg \frac{n}{\sqrt{\log n}}?$$
-/
@[category research open, AMS 52]
theorem erdos_604.variants.sqrt_log : answer(sorry) ↔
    (fun n : ℕ => (n : ℝ) / (n : ℝ).log.sqrt) =O[atTop]
      (fun n => (pinnedDistinctDistances n : ℝ)) := by
  sorry

/--
The integer grid shows that $\frac{n}{\sqrt{\log n}}$ would be best possible: there are sets of
$n$ points in $\mathbb{R}^2$ in which every point has $O(\frac{n}{\sqrt{\log n}})$ distinct
distances to the other points. This follows from the bound of Erdős [Er46] on the total number of
distinct distances in the grid (see Erdős Problem 89), since the number of distances from one point
is at most the total number of distances. For $n$ that is not a square, take $n$ points of the
smallest square grid with at least $n$ points.
-/
@[category research solved, AMS 52]
theorem erdos_604.variants.grid_upper_bound :
    (fun n => (pinnedDistinctDistances n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) / (n : ℝ).log.sqrt) := by
  sorry

/--
Katz and Tardos [KaTa04] proved that some point of $A$ has $\gg n^{c-o(1)}$ distinct distances to
the other points of $A$, where
$$c=\frac{48-14e}{55-16e}=0.864137\cdots.$$
-/
@[category research solved, AMS 52]
theorem erdos_604.variants.katz_tardos :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ((48 - 14 * Real.exp 1) / (55 - 16 * Real.exp 1) - ε) ≤
        (pinnedDistinctDistances n : ℝ) := by
  sorry

/--
Let $d(x)$ be the number of distinct distances from $x$ to the other points of $A$. Erdős [Er75f]
conjectured that
$$\sum_{x\in A}d(x) \gg \frac{n^2}{\sqrt{\log n}}$$
for every set $A\subset\mathbb{R}^2$ of $n$ points.

The sum is at most $n$ times the largest $d(x)$, so this conjecture implies a positive answer to
`Erdos604.erdos_604.variants.sqrt_log`.
-/
@[category research open, AMS 52]
theorem erdos_604.variants.average :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n →
      C * (n : ℝ) ^ 2 / (n : ℝ).log.sqrt ≤ ((∑ x ∈ A, distinctDistancesFrom A x : ℕ) : ℝ) := by
  sorry

end Erdos604
