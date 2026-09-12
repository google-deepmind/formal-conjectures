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
# Erdős Problem 1042

*References:*
- [erdosproblems.com/1042](https://www.erdosproblems.com/1042)
- [EHP58] Erdős, P. and Herzog, F. and Piranian, G., *Metric properties of polynomials*.
  J. Analyse Math. (1958), 125-148.
- [GhRa24] Ghosh, Subhajit and Ramachandran, Koushik, *Number of components of polynomial
  lemniscates: a problem of Erdős, Herzog, and Piranian*. J. Math. Anal. Appl. (2024),
  Paper No. 128571, 21.
-/

open Polynomial Filter Metric
open scoped ENNReal

namespace Erdos1042

/--
The $n$-point transfinite diameter of $F\subseteq\mathbb{C}$,
$$\sup_{z_1,\ldots,z_n\in F}\left(\prod_{i<j}\lvert z_i-z_j\rvert\right)^{1/\binom{n}{2}}.$$
-/
noncomputable def nthTransfiniteDiameter (F : Set ℂ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ z : Fin n → F,
    (∏ i : Fin n, ∏ j : Fin n,
      if i < j then ENNReal.ofReal ‖(z i : ℂ) - (z j : ℂ)‖ else 1) ^ (n.choose 2 : ℝ)⁻¹

/--
The transfinite diameter of $F\subseteq\mathbb{C}$, also known as the logarithmic capacity,
$$\rho(F)=\lim_{n\to \infty}\sup_{z_1,\ldots,z_n\in F}\left(\prod_{i<j}\lvert z_i-z_j\rvert\right)^{1/\binom{n}{2}}.$$
This is a `Filter.limsup`, which agrees with the limit when the latter exists.
-/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ≥0∞ :=
  Filter.limsup (nthTransfiniteDiameter F) atTop

/-- The filled unit lemniscate $\{ z: \lvert f(z)\rvert < 1\}$. -/
def openLevelSet (f : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ < 1}

/-- The connected components of a set `s ⊆ ℂ`, viewed as subsets of `ℂ`. -/
def componentsIn (s : Set ℂ) : Set (Set ℂ) :=
  {t : Set ℂ | ∃ z ∈ s, t = connectedComponentIn s z}

/-- A monic polynomial $f(z)=\prod_{i=1}^{n}(z-z_i)$ with all $z_i\in F$. -/
def IsMonicWithRootsIn (F : Set ℂ) (n : ℕ) (f : ℂ[X]) : Prop :=
  ∃ z : Fin n → ℂ, (∀ i, z i ∈ F) ∧ f = ∏ i, (X - C (z i))

/-- The real interval $[a,b]$, viewed as a subset of $\mathbb{C}$. -/
def realInterval (a b : ℝ) : Set ℂ :=
  (fun x : ℝ ↦ (x : ℂ)) '' Set.Icc a b

/--
Let $F\subset\mathbb{C}$ be a closed set of transfinite diameter $1$ which is not contained
in any closed disc of radius $1$.

If $f(z)=\prod_{i=1}^n(z-z_i)\in\mathbb{C}[x]$ with all $z_i\in F$ then can
$$\{ z: \lvert f(z)\rvert < 1\}$$
have $n$ connected components?

A problem of Erdős, Herzog, and Piranian [EHP58], who proved that if $F$ is the disc of
radius $1$ then this set can have $n$ connected components (for example $f(z)=z^n+1$).

This was solved by Ghosh and Ramachandran [GhRa24], who proved that there are examples with
$d=1$ such that, for infinitely many $n$, the set can have $n$ connected components.
-/
@[category research solved, AMS 30]
theorem erdos_1042.parts.i : answer(True) ↔
    ∃ F : Set ℂ, IsClosed F ∧ transfiniteDiameter F = 1 ∧
      (∀ c : ℂ, ¬ F ⊆ closedBall c 1) ∧
      {n : ℕ | ∃ f : ℂ[X], IsMonicWithRootsIn F n f ∧
        (componentsIn (openLevelSet f)).ncard = n}.Infinite := by
  sorry

/--
If the transfinite diameter of $F$ is $<1$ then must this set only have at most $(1-c)n$
connected components, where $c>0$ depends only on $F$ (or just the transfinite diameter of $F$)?

This was solved by Ghosh and Ramachandran [GhRa24], who proved that, if $d$ is the transfinite
diameter of $F$, then if $0<d<1$ then the set has at most $(1-c)n$ connected components for some
$c>0$ depending on $F$.
-/
@[category research solved, AMS 30]
theorem erdos_1042.parts.ii : answer(True) ↔
    ∀ (F : Set ℂ), IsClosed F → transfiniteDiameter F < 1 →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ f : ℂ[X], IsMonicWithRootsIn F n f →
        ((componentsIn (openLevelSet f)).ncard : ℝ) ≤ (1 - c) * n := by
  sorry

/--
A problem of Erdős, Herzog, and Piranian [EHP58], who proved that if $F$ is the disc of
radius $1$ then this set can have $n$ connected components (for example $f(z)=z^n+1$).
-/
@[category research solved, AMS 30]
theorem erdos_1042.variants.unit_disc (n : ℕ) (hn : 0 < n)
    (f : ℂ[X]) (hf : f = (X : ℂ[X]) ^ n + 1) :
    IsMonicWithRootsIn (closedBall (0 : ℂ) 1) n f ∧
      (componentsIn (openLevelSet f)).ncard = n := by
  sorry

/--
If $d\leq 1/4$ and $F$ is connected then the set has only one connected component.
-/
@[category research solved, AMS 30]
theorem erdos_1042.variants.connected_le_quarter (F : Set ℂ) (hF : IsClosed F)
    (hconn : IsConnected F) (hd : transfiniteDiameter F ≤ 1 / 4) (n : ℕ) (hn : 0 < n)
    (f : ℂ[X]) (hf : IsMonicWithRootsIn F n f) :
    (componentsIn (openLevelSet f)).ncard = 1 := by
  sorry

/--
They also note that the answer cannot depend only on the transfinite diameter of $F$ - for
example, both $F_1=\{ z: \lvert z\rvert\leq 1/2\}$ and $F_2=[-1,1]$ have transfinite diameter
$1/2$, but the former always has one connected component, and the latter can have $\gg n$ many
connected components.
-/
@[category research solved, AMS 30]
theorem erdos_1042.variants.disc_vs_interval :
    transfiniteDiameter (closedBall (0 : ℂ) (1 / 2)) = 1 / 2 ∧
    transfiniteDiameter (realInterval (-1) 1) = 1 / 2 ∧
    (∀ n : ℕ, 0 < n → ∀ f : ℂ[X], IsMonicWithRootsIn (closedBall (0 : ℂ) (1 / 2)) n f →
      (componentsIn (openLevelSet f)).ncard = 1) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∃ f : ℂ[X],
      IsMonicWithRootsIn (realInterval (-1) 1) n f ∧
        c * n ≤ ((componentsIn (openLevelSet f)).ncard : ℝ) := by
  sorry

end Erdos1042
