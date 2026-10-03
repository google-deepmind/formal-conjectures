/-
Copyright 2025 The Formal Conjectures Authors.

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

A problem of Erdős, Faudree, Rousseau, and Schelp on the growth exponent of the largest clique
that is guaranteed inside a locally dense graph.

*References:*
* [erdosproblems.com/667](https://www.erdosproblems.com/667)
* [Er97f] P. Erdős, _Some old and new problems in various branches of combinatorics_.
  Discrete Math. 165/166 (1997), 227-231.
* [EFRS94] P. Erdős, R. J. Faudree, C. C. Rousseau and R. H. Schelp,
  _A local density condition for triangles_. Discrete Math. 127 (1994), 153-161.
-/

open SimpleGraph Filter
open scoped Classical

namespace Erdos667

/-- A graph `G` on `n` vertices is *`(p, q)`-locally dense* if every set of `p` of its vertices
spans at least `q` edges of `G`; equivalently, every induced subgraph on `p` vertices has at
least `q` edges. -/
def LocallyDense (p q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), s.card = p → q ≤ (G.induce s).edgeSet.ncard

/-- `H p q n` is `H(n) = H(n; p, q)`: the largest `m` such that *every* `(p, q)`-locally dense
graph on `n` vertices must contain a complete graph on `m` vertices `Kₘ`.

The condition "`G` contains `Kₘ`" is `¬ G.CliqueFree m`. Any `m`-clique needs `m ≤ n` vertices,
and the property is downward closed in `m`, so `Nat.findGreatest _ n` returns the genuine maximum. -/
noncomputable def H (p q n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun m => ∀ G : SimpleGraph (Fin n), LocallyDense p q G → ¬ G.CliqueFree m) n

/-- The growth exponent `c(p, q) = liminf_{n → ∞} (log H(n)) / (log n)`. -/
noncomputable def c (p q : ℕ) : ℝ :=
  liminf (fun n : ℕ => Real.log (H p q n) / Real.log n) atTop

/--
Let $p, q \geq 1$ be fixed integers. Define $H(n) = H(n; p, q)$ to be the largest $m$ such that any
graph on $n$ vertices where every set of $p$ vertices spans at least $q$ edges must contain a
complete graph on $m$ vertices. Is
$$ c(p, q) = \liminf_{n \to \infty} \frac{\log H(n)}{\log n} $$
a strictly increasing function of $q$ for $1 \leq q \leq \binom{p-1}{2} + 1$?

A problem of Erdős, Faudree, Rousseau, and Schelp. When $q = 1$ this corresponds exactly to the
classical Ramsey problem, and hence $\tfrac{1}{p-1} \leq c(p, 1) \leq \tfrac{2}{p+1}$. It is easy
to see that if $q = \binom{p-1}{2} + 1$ then $c(p, q) = 1$. Erdős, Faudree, Rousseau and Schelp
have shown that $c(p, \binom{p-1}{2}) \leq 1/2$.
-/
@[category research open, AMS 5]
theorem erdos_667 :
    answer(sorry) ↔
      ∀ p : ℕ, StrictMonoOn (c p) (Set.Icc 1 (Nat.choose (p - 1) 2 + 1)) := by
  sorry

/--
That $c(p, q)$ is *nondecreasing* in $q$ for fixed $p$ is a straightforward consequence of the
definitions: enlarging $q$ shrinks the family of $(p, q)$-locally dense graphs, which can only
increase the guaranteed clique size $H(n)$, and hence the exponent.
-/
@[category research solved, AMS 5]
theorem erdos_667.variants.monotoneOn (p : ℕ) :
    MonotoneOn (c p) (Set.Icc 1 (Nat.choose (p - 1) 2 + 1)) := by
  sorry

/--
The right endpoint: when $q = \binom{p-1}{2} + 1$ one has $c(p, q) = 1$
(stated as "easy to see" on erdosproblems.com/667).
-/
@[category research solved, AMS 5]
theorem erdos_667.variants.endpoint (p : ℕ) (hp : 2 ≤ p) :
    c p (Nat.choose (p - 1) 2 + 1) = 1 := by
  sorry

/--
The case $q = 1$ is the classical Ramsey problem, giving the bounds
$\tfrac{1}{p-1} \leq c(p, 1) \leq \tfrac{2}{p+1}$.
-/
@[category research solved, AMS 5]
theorem erdos_667.variants.ramsey_bounds (p : ℕ) (hp : 2 ≤ p) :
    1 / ((p : ℝ) - 1) ≤ c p 1 ∧ c p 1 ≤ 2 / ((p : ℝ) + 1) := by
  sorry

end Erdos667
