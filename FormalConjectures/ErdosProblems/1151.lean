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
# Erdős Problem 1151

*Reference:* [erdosproblems.com/1151](https://www.erdosproblems.com/1151)

Let $\mathcal{L}^n f(x) = \sum_{i} f(a_i) \ell_i(x)$ be the Lagrange interpolation
polynomial of degree $n-1$ agreeing with $f$ at the $n$ Chebyshev nodes.

Erdős [Er41] proved that for $x = \cos(\pi p/q)$ with $p, q$ odd, there is a continuous
$f$ with $\lim_{n \to \infty} \mathcal{L}^n f(x) = \infty$. In [Er43] he claims
(without proof) that for any closed set $A$ there exists continuous $f$ achieving $A$
as the limit set.

[Er41] Erdős, P., _On divergence properties of the Lagrange interpolation parabolas_.
Annals of Mathematics, Series 2 (1941), 309–315.

[Er43] Erdős, P., _A note on Farey series_. Quarterly Journal of Mathematics, Oxford
Series (1943), 82–85.

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
"Paul Erdős and his mathematics," Budapest, July 1999.
-/

open Classical Finset BigOperators Filter

open scoped Topology

namespace Erdos1151

/-- The $k$-th Chebyshev node of order $n$ (0-indexed):
$\cos((2k + 1)\pi / (2n))$ for $k = 0, \ldots, n-1$. -/
noncomputable def chebyshevNode (n : ℕ) (k : Fin n) : ℝ :=
  Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * (n : ℝ)))

/-- The Lagrange basis polynomial $\ell_i(x) = \prod_{j \neq i} (x - x_j)/(x_i - x_j)$. -/
noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (x - nodes j) / (nodes i - nodes j)

/-- The Lagrange interpolation of $f$ at the given nodes, evaluated at $x$:
$L(x) = \sum_i f(x_i) \cdot \ell_i(x)$. -/
noncomputable def lagrangeInterp {n : ℕ} (nodes : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, f (nodes i) * lagrangeBasis nodes i x

/--
Erdős Problem 1151 [Va99, 2.41]:
For any $x \in [-1,1]$ and any closed $A \subseteq [-1,1]$, there exists a continuous
function $f$ such that $A$ is the set of cluster points of the Lagrange interpolation
polynomials $L^n f(x)$ at the Chebyshev nodes as $n \to \infty$.
-/
@[category research open, AMS 26 41]
theorem erdos_1151 (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (A : Set ℝ) (hA : IsClosed A) (hAsub : A ⊆ Set.Icc (-1 : ℝ) 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      {y | MapClusterPt y atTop (fun n => lagrangeInterp (chebyshevNode (n + 1)) f x)} = A := by
  sorry

/--
Variant of Erdős Problem 1151 restricted to the special points from [Er41]:
For $x = \cos(\pi p / q)$ with $p, q$ odd positive integers and any closed
$A \subseteq [-1,1]$, there exists a continuous function $f$ such that $A$ is
the set of cluster points of the Lagrange interpolation polynomials at the
Chebyshev nodes. This is the more conservative reading of Erdős's claim in [Er43].
-/
@[category research open, AMS 26 41]
theorem erdos_1151_variant (p q : ℕ) (hp : Odd p) (hq : Odd q) (hq_pos : 0 < q)
    (A : Set ℝ) (hA : IsClosed A) (hAsub : A ⊆ Set.Icc (-1 : ℝ) 1) :
    let x := Real.cos (↑p * Real.pi / ↑q)
    ∃ f : ℝ → ℝ, Continuous f ∧
      {y | MapClusterPt y atTop (fun n => lagrangeInterp (chebyshevNode (n + 1)) f x)} = A := by
  sorry

end Erdos1151
