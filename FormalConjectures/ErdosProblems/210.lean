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
# Erdős Problem 210

Let $f(n)$ denote the minimum number of ordinary lines determined by $n$
non-collinear points in the plane. Erdős asked whether $f(n) \to \infty$ and
how fast it grows.

*Reference:* [erdosproblems.com/210](https://www.erdosproblems.com/210)
-/

open Classical

namespace Erdos210

/-- Points in the Euclidean plane $\mathbb{R}^2$. -/
abbrev Point2 := EuclideanSpace ℝ (Fin 2)

/-- Point $r$ lies on the line through distinct points $p$ and $q$. -/
def LiesOnLine (p q r : Point2) : Prop :=
  ∃ t : ℝ, r - p = t • (q - p)

/-- A finite set of points is not all collinear: there exist three
non-collinear points in $S$. -/
def NotAllCollinear (S : Finset Point2) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ ¬LiesOnLine p q r

/-- An ordered pair $(p, q)$ determines an ordinary line for $S$ if $p \neq q$,
both lie in $S$, and no third point of $S$ lies on the line through $p$ and $q$. -/
def IsOrdinaryPair (S : Finset Point2) (p q : Point2) : Prop :=
  p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ ∀ r ∈ S, r ≠ p → r ≠ q → ¬LiesOnLine p q r

/-- The number of ordinary lines determined by $S$.
Counts ordered pairs forming ordinary lines and divides by $2$. -/
noncomputable def ordinaryLineCount (S : Finset Point2) : ℕ :=
  ((S ×ˢ S).filter (fun pq => IsOrdinaryPair S pq.1 pq.2)).card / 2

/--
Let $f(n)$ be minimal such that for any $n$ points in $\mathbb{R}^2$, not all on a line,
there are at least $f(n)$ ordinary lines (lines containing exactly $2$ of the
points). Green and Tao proved that $f(n) \geq n/2$ for all sufficiently large $n$,
resolving the conjecture of Erdős and de Bruijn and strengthening earlier
results of Motzkin ($f(n) \to \infty$), Kelly-Moser ($f(n) \geq 3n/7$), and
Csima-Sawyer ($f(n) \geq 6n/13$).
-/
@[category research solved, AMS 5 52]
theorem erdos_210 :
    ∃ N₀ : ℕ, ∀ (S : Finset Point2),
      S.card ≥ N₀ →
      NotAllCollinear S →
      ordinaryLineCount S ≥ S.card / 2 := by
  sorry

end Erdos210
