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
# Erdős Problem 1166

*Reference:* [erdosproblems.com/1166](https://www.erdosproblems.com/1166)

For a simple random walk on $\mathbb{Z}^2$, a *favourite site* at time $k$ is a site with the
maximum number of visits up to time $k$. The problem asks whether the cumulative number of
distinct favourite sites $\left|\bigcup_{k \le n} F(k)\right|$ is bounded by a power of $\log n$
almost surely, for all but finitely many $n$.

[Va99] Varga, L., *Problems and results on random walks*, 1999.

[ErTa60] Erdős, P. and Taylor, S. J., *Some problems concerning the structure of random walk
paths*, Acta Math. Acad. Sci. Hungar. 11, 137–162, 1960.
-/

open MeasureTheory ProbabilityTheory Filter Finset

open scoped BigOperators

namespace Erdos1166

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A step distribution for a simple random walk on $\mathbb{Z}^2$: the random variable takes
    values in $\{(1,0), (-1,0), (0,1), (0,-1)\}$ each with equal probability. -/
def IsUniformStep (μ : Measure Ω) (X : Ω → ℤ × ℤ) : Prop :=
  (∀ ω, X ω ∈ ({((1 : ℤ), 0), (-1, 0), (0, 1), (0, -1)} : Set (ℤ × ℤ))) ∧
  μ {ω | X ω = (1, 0)} = μ {ω | X ω = (-1, 0)} ∧
  μ {ω | X ω = (-1, 0)} = μ {ω | X ω = (0, 1)} ∧
  μ {ω | X ω = (0, 1)} = μ {ω | X ω = (0, -1)}

/-- Position of the random walk at time $n$: $S_n = X_0 + X_1 + \cdots + X_{n-1}$,
    starting at the origin $S_0 = (0, 0)$. -/
def walkPosition (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : ℤ × ℤ :=
  ∑ i ∈ Finset.range n, X i ω

/-- The local time (visit count) at site $x$ up to time $k$:
    $f_k(x) = |\{l : 0 \le l \le k \mid S_l = x\}|$. -/
def localTime (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (k : ℕ) (x : ℤ × ℤ) : ℕ :=
  ((Finset.range (k + 1)).filter (fun l => walkPosition X ω l = x)).card

/-- The set of sites visited by the walk up to time $k$. -/
def visitedSites (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (k + 1)).image (fun l => walkPosition X ω l)

/-- The maximum local time at time $k$:
    $\max_y f_k(y)$, the maximum number of visits to any single site. -/
def maxLocalTime (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (k : ℕ) : ℕ :=
  (visitedSites X ω k).sup (localTime X ω k)

/-- The set of favourite sites at time $k$:
    $F(k) = \{x \in \text{visited sites} : f_k(x) = \max_y f_k(y)\}$. -/
def favouriteSites (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (k : ℕ) : Finset (ℤ × ℤ) :=
  (visitedSites X ω k).filter (fun x => localTime X ω k x = maxLocalTime X ω k)

/-- The cumulative set of favourite sites up to time $n$:
    $\bigcup_{k \le n} F(k)$, the set of all sites that were ever a favourite site. -/
def cumulativeFavouriteSites (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (n + 1)).biUnion (fun k => favouriteSites X ω k)

/--
Erdős Problem 1166 (Erdős–Révész) [Va99, 6.78]:

Given a random walk $s_0, s_1, \ldots$ in $\mathbb{Z}^2$, starting at the origin, let $f_k(x)$
count the number of $0 \le l \le k$ such that $s_l = x$. Let
$F(k) = \{x : f_k(x) = \max_y f_k(y)\}$ be the set of 'favourite sites'. Is it true that
$$\left|\bigcup_{k \le n} F(k)\right| \le (\log n)^{O(1)}$$
almost surely, for all but finitely many $n$?

This is true: almost surely $\left|\bigcup_{k \le n} F(k)\right| \ll (\log n)^2$, which follows
from the fact that almost surely $|F(n)| \le 3$ for all large $n$ (see Erdős Problem 1165) and
the result of Erdős and Taylor [ErTa60] that the maximum number of visits to any fixed point
by time $n$ is $\ll (\log n)^2$.
-/
@[category research solved, AMS 60]
theorem erdos_1166 : answer(True) ↔
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℤ × ℤ),
    (∀ i, IsUniformStep μ (X i)) →
    iIndepFun X μ →
    ∃ C : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ (n : ℕ) in atTop,
      ((cumulativeFavouriteSites X ω n).card : ℝ) ≤ Real.log (n : ℝ) ^ C := by
  sorry

end Erdos1166
