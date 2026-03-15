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
# Erdős Problem 1165

*Reference:* [erdosproblems.com/1165](https://www.erdosproblems.com/1165)

Given a random walk on $\mathbb{Z}^2$, the *favourite sites* $F(n)$ are those visited the
maximum number of times up to step $n$. Tóth proved that $|F(n)| = r$ occurs only finitely
often almost surely for every $r \ge 4$, and Hao–Li–Okada–Zheng proved that $|F(n)| = 3$
occurs infinitely often almost surely.

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
"Paul Erdős and his mathematics", Budapest, July 1999 (1999), §6.77.

[To01] Tóth, B., _No more than three favorite sites for simple random walk_.
Ann. Probab. (2001), 484–503.

[HLOZ24] Hao, C., Li, X., Okada, I., Zheng, Y., _Favorite sites for simple random walk
in two and more dimensions_. arXiv:2409.00995 (2024).
-/

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

namespace Erdos1165

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

/-- The local time (visit count) at site $x$ up to time $n$:
$f_n(x) = |\{k : 0 \le k \le n \mid S_k = x\}|$. -/
def localTime (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) (x : ℤ × ℤ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => walkPosition X ω k = x)).card

/-- The set of sites visited by the walk up to time $n$. -/
def visitedSites (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (n + 1)).image (fun k => walkPosition X ω k)

/-- The maximum local time at time $n$:
$\max_y f_n(y)$, the maximum number of visits to any single site. -/
def maxLocalTime (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : ℕ :=
  (visitedSites X ω n).sup (localTime X ω n)

/-- The set of favourite sites at time $n$:
$F(n) = \{x \in \text{visited sites} : f_n(x) = \max_y f_n(y)\}$. -/
def favouriteSites (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (n : ℕ) : Finset (ℤ × ℤ) :=
  (visitedSites X ω n).filter (fun x => localTime X ω n x = maxLocalTime X ω n)

/--
Erdős Problem 1165 (Erdős–Révész) [Va99, 6.77]:

Given a random walk $s_0, s_1, \ldots$ in $\mathbb{Z}^2$, starting at the origin, let $f_n(x)$
count the number of $0 \le k \le n$ such that $s_k = x$. Let
$F(n) = \{x : f_n(x) = \max_y f_n(y)\}$ be the set of 'favourite sites'.

Tóth [To01] proved that $|F(n)| = r$ occurs only finitely often almost surely for all $r \ge 4$.
Hao, Li, Okada, and Zheng [HLOZ24] proved that $|F(n)| = 3$ occurs infinitely often almost surely.
-/
@[category research solved, AMS 60]
theorem erdos_1165
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℤ × ℤ}
    (hStep : ∀ i, IsUniformStep μ (X i))
    (hIndep : iIndepFun X μ) :
    -- Part 1: |F(n)| = 3 infinitely often, almost surely
    (∀ᵐ ω ∂μ, ∃ᶠ (n : ℕ) in atTop,
      (favouriteSites X ω n).card = 3) ∧
    -- Part 2: |F(n)| = r for r ≥ 4 happens only finitely often, almost surely
    (∀ r : ℕ, r ≥ 4 →
      ∀ᵐ ω ∂μ, ¬∃ᶠ (n : ℕ) in atTop,
        (favouriteSites X ω n).card = r) := by
  sorry

end Erdos1165
