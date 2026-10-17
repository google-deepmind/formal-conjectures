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
# Erdős Problem 589

*References:*
- [erdosproblems.com/589](https://www.erdosproblems.com/589)
- [Fu91b] Füredi, Zoltán, *Maximal independent subsets in Steiner systems and in planar
  sets*. SIAM J. Discrete Math. (1991), 196–199.
- [BaSo18] Balogh, József and Solymosi, József, *On the number of points in general
  position in the plane*. Discrete Anal. (2018), Paper No. 16, 20.
-/

@[expose] public section

open EuclideanGeometry Filter Asymptotics

namespace Erdos589

/-- The largest $m \leq n$ such that every set of $n$ points in $\mathbb{R}^2$ with no
four points on a line contains a subset of $m$ points with no three points on a line. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {m | m ≤ n ∧ ∀ S : Finset ℝ², S.card = n → NonCollinearFor 4 (S : Set ℝ²) →
    ∃ T ⊆ S, T.card = m ∧ NonCollinearFor 3 (T : Set ℝ²)}

/-- The guaranteed subset has at most $n$ points. -/
@[category API, AMS 5 52]
lemma g_le (n : ℕ) : g n ≤ n := by
  unfold g
  exact csSup_le' fun _ hm => hm.1

/-- The empty point set gives $g(0)=0$. -/
@[simp, category API, AMS 5 52]
lemma g_zero : g 0 = 0 :=
  Nat.eq_zero_of_le_zero (g_le 0)

/--
Let $g(n)$ be maximal such that in any set of $n$ points in $\mathbb{R}^2$ with no four
points on a line there exists a subset on $g(n)$ points with no three points on a line.
Estimate $g(n)$.

This asks for an asymptotic lower bound.
-/
@[category research open, AMS 5 52]
theorem erdos_589.lower_bound :
    (answer(sorry) : ℕ → ℝ) =O[atTop] (fun n => (g n : ℝ)) := by
  sorry

/-- Estimate $g(n)$: this asks for an asymptotic upper bound. -/
@[category research open, AMS 5 52]
theorem erdos_589.upper_bound :
    (fun n => (g n : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Füredi [Fu91b] proved $\sqrt{n\log n}\ll g(n)$. -/
@[category research solved, AMS 5 52]
theorem erdos_589.variants.furedi_lower_bound :
    (fun n : ℕ => Real.sqrt ((n : ℝ) * Real.log n)) =O[atTop]
      (fun n => (g n : ℝ)) := by
  sorry

/-- Erdős thought that $g(n)\gg n$, but in fact $g(n)=o(n)$.
Füredi [Fu91b] proved this using the density Hales–Jewett theorem. -/
@[category research solved, AMS 5 52]
theorem erdos_589.variants.sublinear :
    (fun n => (g n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  sorry

/-- Balogh and Solymosi [BaSo18] improved the upper bound to
$g(n)\ll n^{5/6+o(1)}$. Equivalently, for every $\varepsilon>0$,
$g(n)\ll n^{5/6+\varepsilon}$. -/
@[category research solved, AMS 5 52]
theorem erdos_589.variants.balogh_solymosi :
    ∀ ε : ℝ, 0 < ε → (fun n => (g n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (5 / 6 + ε : ℝ)) := by
  sorry

end Erdos589
