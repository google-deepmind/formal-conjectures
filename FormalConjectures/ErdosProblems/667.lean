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
# Erdős Problem 667

*Reference:* [erdosproblems.com/667](https://www.erdosproblems.com/667)

Let $p, q \geq 1$ be fixed integers. Define $H(n) = H(n; p, q)$ to be the largest $m$
such that any graph on $n$ vertices where every set of $p$ vertices spans at least
$q$ edges must contain a complete graph on $m$ vertices.

Is $c(p, q) = \liminf_{n \to \infty} \frac{\log H(n; p, q)}{\log n}$ a strictly increasing
function of $q$ for $1 \leq q \leq \binom{p-1}{2} + 1$?

A problem of Erdős, Faudree, Rousseau, and Schelp [Er97f].

[Er97f] Erdős, P., Faudree, R., Rousseau, C., and Schelp, R.
-/

open SimpleGraph Finset Filter Classical

namespace Erdos667

/-- The number of edges of $G$ within a subset $S$ of vertices:
the count of pairs $(u, v)$ with $u < v$, both in $S$, that are adjacent in $G$. -/
noncomputable def edgesInSubset {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ S).filter fun e => e.1 < e.2 ∧ G.Adj e.1 e.2).card

/-- A graph on $n$ vertices has the $(p, q)$-density property if every $p$-element
subset spans at least $q$ edges. -/
def HasDensityProperty {n : ℕ} (G : SimpleGraph (Fin n)) (p q : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = p → edgesInSubset G S ≥ q

/-- $H(n; p, q)$: the largest $m$ such that every graph on $n$ vertices with the
$(p, q)$-density property must contain a clique of size $m$. -/
noncomputable def erdosH (n p q : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ G : SimpleGraph (Fin n),
    HasDensityProperty G p q → ∃ S : Finset (Fin n), G.IsNClique m S}

/-- $c(p, q) = \liminf_{n \to \infty} \frac{\log H(n; p, q)}{\log n}$. -/
noncomputable def erdosC (p q : ℕ) : ℝ :=
  Filter.liminf (fun n : ℕ => Real.log (erdosH n p q : ℝ) / Real.log (n : ℝ))
    Filter.atTop

/--
Erdős Problem 667 [Er97f]:

Is $c(p, q)$ strictly increasing in $q$ for $1 \leq q \leq \binom{p-1}{2} + 1$?

That is, for all $q$ with $1 \leq q < \binom{p-1}{2} + 1$, we have $c(p, q) < c(p, q+1)$.
-/
@[category research open, AMS 5]
theorem erdos_667 : answer(sorry) ↔
    ∀ (p : ℕ), p ≥ 1 → ∀ (q : ℕ), 1 ≤ q → q < (p - 1).choose 2 + 1 →
    erdosC p q < erdosC p (q + 1) := by
  sorry

end Erdos667
