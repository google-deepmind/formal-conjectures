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
# Erdős Problem 1066

*References:*
- [erdosproblems.com/1066](https://www.erdosproblems.com/1066)
- [Cs98] Csizmadia, G., *On the independence number of minimum distance graphs*.
  Discrete Comput. Geom. 20 (1998), 179-187.
- [Er87b] Erdős, P., *Some combinatorial and metric problems in geometry*.
  Intuitive geometry (Siófok, 1985) (1987), 167-177.
- [PaTo96] Pach, J. and Tóth, G., *On the independence number of coin graphs*.
  Geombinatorics 6 (1996), 30-33.
- [Po85] Pollack, R., *Increasing the minimum distance of a set of points*.
  J. Combin. Theory Ser. A 40 (1985), 450.
- [Sw02] Swanepoel, K. J., *Independence numbers of planar contact graphs*.
  Discrete Comput. Geom. 28 (2002), 649-670.
-/

@[expose] public section

open Filter SimpleGraph
open scoped EuclideanGeometry Topology

namespace Erdos1066

/-- $g(n)$: the largest $m$ such that, for every set $X$ of $n$ points of $\mathbb{R}^2$ with any
two distinct points at distance at least $1$, the graph on $X$ joining points at distance exactly
$1$ has an independent set with at least $m$ vertices. The set of such $m$ contains $0$ and is
bounded by $n$, so `sSup` is a true maximum. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ X : Finset ℝ², X.card = n →
    (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y) →
      m ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum}

/-- For every admissible point set `X`, $g(|X|)$ is at most the independence number of its unit
distance graph. -/
@[category API, AMS 5 52]
theorem g_le (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)) :
    g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum := by
  refine csSup_le ⟨0, fun _ _ _ => Nat.zero_le _⟩ ?_
  intro m hm
  exact hm X rfl hX

/-- $g_d(n)$: the largest $m$ such that every set $X$ of $n$ points of $\mathbb{R}^d$ with any two
distinct points at distance at least $1$ contains at least $m$ points with pairwise distances
greater than $1$. For $d \geq 1$ the set of such $m$ contains $0$ and is bounded by $n$, so `sSup`
is a true maximum. -/
noncomputable def gDim (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ X : Finset (ℝ^d), X.card = n →
    (X : Set (ℝ^d)).Pairwise (fun x y ↦ 1 ≤ dist x y) →
      ∃ Y ⊆ X, m ≤ Y.card ∧ (Y : Set (ℝ^d)).Pairwise (fun x y ↦ 1 < dist x y)}

def erdos_1066.answer : ℝ := sorry

/--
Let $G$ be a graph given by $n$ points in $\mathbb{R}^2$, where any two distinct points are at
least distance $1$ apart, and we draw an edge between two points if they are distance $1$ apart.

Let $g(n)$ be maximal such that any such graph always has an independent set on at least $g(n)$
vertices. Estimate $g(n)$, or perhaps $\lim \frac{g(n)}{n}$.

We ask for $\lim g(n)/n$. The limit exists by Fekete's lemma, since placing two configurations far
apart shows $g(a+b) \leq g(a)+g(b)$.
-/
@[category research open, question value, AMS 5 52]
theorem erdos_1066 :
    Tendsto (fun n : ℕ ↦ (g n : ℝ) / n) atTop (𝓝 erdos_1066.answer) := by
  sorry

/--
Such graphs are always planar. Pollack [Po85] noted that the Four colour theorem implies
$g(n)\geq n/4$, since the graph is planar.
-/
@[category research solved, AMS 5 52]
theorem erdos_1066.variants.pollack (n : ℕ) : (n : ℝ) / 4 ≤ (g n : ℝ) := by
  sorry

/--
This lower bound has been improved to $\frac{9}{35}n$ by Csizmadia [Cs98] and then
$\frac{8}{31}n$ by Swanepoel [Sw02].
-/
@[category research solved, AMS 5 52]
theorem erdos_1066.variants.swanepoel (n : ℕ) : (8 / 31 : ℝ) * n ≤ (g n : ℝ) := by
  sorry

/--
Erdős initially thought that $g(n)=n/3$, but Chung and Graham, and independently Pach, gave a
construction that shows $g(n)\leq \frac{6}{19}n$. Pach and Tóth [PaTo96] improved this to
$g(n)\leq \frac{5}{16}n$.

Since $g(1) = 1$, the bound cannot hold for all $n$, so it is stated for infinitely many $n$,
with $5/16$ replaced by $5/16+\varepsilon$ for every $\varepsilon > 0$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1066.variants.pach_toth :
    ∀ ε > (0 : ℝ), ∃ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (5 / 16 + ε) * n := by
  sorry

/--
Pollack [Po85] also reports a letter from Erdős which poses the more general problem of, given
$n$ points in $\mathbb{R}^d$ with minimum distance $1$, let $g_d(n)$ be maximal such that there
always exist at least $g_d(n)$ many points which have minimum distance $>1$. Is it true that
$g_d(n) \gg n/d$ in general?

We read this with a constant independent of $d$ and $n$.
-/
@[category research open, question, AMS 52]
theorem erdos_1066.variants.higher_dim :
    ∃ c > (0 : ℝ), ∀ d n : ℕ, 1 ≤ d → c * n / d ≤ (gDim d n : ℝ) := by
  sorry

end Erdos1066
