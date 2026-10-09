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
# Erdős Problem 766

*References:*
- [erdosproblems.com/766](https://www.erdosproblems.com/766)
- [Er64c] Erdős, P., *Extremal problems in graph theory*. Theory of Graphs and its Applications
  (Proc. Sympos. Smolenice, 1963) (1964), 29-36.
-/

@[expose] public section

open Filter

namespace Erdos766

/-- $f(n;k,l)$: the minimum of $\mathrm{ex}(n;G)$ over all graphs $G$ with $k$ vertices and $l$
edges. Here $\mathrm{ex}(n;G)$ is `SimpleGraph.extremalNumber n G`, the maximum number of edges
of a graph on $n$ vertices with no (not necessarily induced) copy of $G$. The value is in `ℕ∞` and
is `⊤` when no such graph $G$ exists. -/
noncomputable def minExtremalNumber (n k l : ℕ) : ℕ∞ :=
  ⨅ (G : SimpleGraph (Fin k)) (_ : G.edgeSet.ncard = l), (SimpleGraph.extremalNumber n G : ℕ∞)

/-- $f(n;k,l) \leq \mathrm{ex}(n;G)$ for every graph $G$ with $k$ vertices and $l$ edges. -/
@[category API, AMS 5]
theorem minExtremalNumber_le (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k))
    (h : G.edgeSet.ncard = l) : minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G :=
  iInf₂_le G h

/-- There is no graph with $0$ vertices and $1$ edge, so $f(n;0,1) = \top$. -/
@[category test, AMS 5]
theorem minExtremalNumber_zero_one (n : ℕ) : minExtremalNumber n 0 1 = ⊤ := by
  simp [minExtremalNumber, Set.eq_empty_of_isEmpty]

/--
Let $f(n;k,l)=\min \mathrm{ex}(n;G)$, where $G$ ranges over all graphs with $k$ vertices and $l$
edges.

Give good estimates for $f(n;k,l)$ in the range $k<l\leq k^2/4$.
-/
@[category research open, AMS 5]
theorem erdos_766.parts.i :
    let f : ℕ → ℕ → ℕ → ℝ := answer(sorry)
    ∀ k l : ℕ, k < l → l ≤ k ^ 2 / 4 →
      (fun n ↦ ((minExtremalNumber n k l).toNat : ℝ)) =Θ[atTop] f k l := by
  sorry

/--
For fixed $k$ and large $n$ is $f(n;k,l)$ a strictly monotone function of $l$?

We use the range $k<l\leq k^2/4$ of `Erdos766.erdos_766.parts.i`; here `k ^ 2 / 4` is
$\lfloor k^2/4\rfloor$.
-/
@[category research open, AMS 5]
theorem erdos_766.parts.ii : answer(sorry) ↔
    ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      StrictMonoOn (minExtremalNumber n k) (Set.Ioc k (k ^ 2 / 4)) := by
  sorry

/--
Dirac and Erdős proved independently that when $l=\lfloor k^2/4\rfloor+1$
$$f(n;k,l)\leq \lfloor n^2/4\rfloor+1.$$

We assume $k\geq 3$, so that a graph with $k$ vertices and $\lfloor k^2/4\rfloor+1$ edges exists,
and state the bound for all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_766.variants.dirac_erdos (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, minExtremalNumber n k (k ^ 2 / 4 + 1) ≤ ((n ^ 2 / 4 + 1 : ℕ) : ℕ∞) := by
  sorry

end Erdos766
