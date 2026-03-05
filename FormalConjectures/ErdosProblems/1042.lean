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
# Erdős Problem 1042

*Reference:* [erdosproblems.com/1042](https://www.erdosproblems.com/1042)

A problem of Erdős, Herzog, and Piranian on the number of connected components
of sublevel sets of monic polynomials with roots in a closed set of prescribed
transfinite diameter.

[EHP58] Erdős, P., Herzog, F., and Piranian, G., _Metric properties of
polynomials_, J. Analyse Math. 6 (1958), 125-148.

[GhRa24] Ghosh, S. and Ramachandran, D., solved both parts of this problem.
-/

open Classical Filter Finset

namespace Erdos1042

/-- The product of pairwise distances $\prod_{i<j} \|z_i - z_j\|$ for a tuple of
complex numbers. -/
noncomputable def pairwiseDistProd {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ((univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)).prod
    (fun p => ‖z p.1 - z p.2‖)

/-- The $n$-th transfinite diameter of $F \subseteq \mathbb{C}$:
$$d_n(F) = \sup_{z_1,\ldots,z_n \in F} \left(\prod_{i<j} |z_i - z_j|\right)^{2/(n(n-1))}.$$ -/
noncomputable def nthTransfiniteDiam (F : Set ℂ) (n : ℕ) : ℝ :=
  sSup {t : ℝ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ F) ∧
    t = (pairwiseDistProd z) ^ ((2 : ℝ) / (↑n * (↑n - 1)))}

/-- The transfinite diameter (logarithmic capacity) of $F \subseteq \mathbb{C}$:
$$\rho(F) = \lim_{n \to \infty} d_n(F).$$ -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ :=
  lim (atTop.map (fun n => nthTransfiniteDiam F n))

/-- The sublevel set $\{z : \|\prod_i(z - z_i)\| < 1\}$ of a monic polynomial with
given roots. -/
def sublevelSet {n : ℕ} (z : Fin n → ℂ) : Set ℂ :=
  {w : ℂ | ‖(univ : Finset (Fin n)).prod (fun i => w - z i)‖ < 1}

/--
Erdős Problem 1042, existence [GhRa24]:

There exists a closed set $F \subset \mathbb{C}$ with transfinite diameter $1$, not contained in
any closed disc of radius $1$, and for infinitely many $n$ there exist $z_1,\ldots,z_n \in F$
such that $\{z : |\prod(z - z_i)| < 1\}$ has exactly $n$ connected components.
-/
@[category research solved, AMS 30 31]
theorem erdos_1042 :
    ∃ (F : Set ℂ), IsClosed F ∧ transfiniteDiameter F = 1 ∧
      (¬∃ c : ℂ, F ⊆ Metric.closedBall c 1) ∧
      Set.Infinite {n : ℕ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ F) ∧
        Nat.card (ConnectedComponents ↥(sublevelSet z)) = n} := by
  sorry

/--
Erdős Problem 1042, upper bound [GhRa24]:

If $F \subset \mathbb{C}$ is closed with $0 < \text{transfinite diameter} < 1$, then there exists
$c > 0$ (depending on $F$) such that for all $n$ and all $z_1,\ldots,z_n \in F$, the number of
connected components of $\{z : |\prod(z - z_i)| < 1\}$ is at most $(1-c) \cdot n$.
-/
@[category research solved, AMS 30 31]
theorem erdos_1042.variants.upper_bound (F : Set ℂ) (hF : IsClosed F)
    (hd_pos : transfiniteDiameter F > 0) (hd_lt : transfiniteDiameter F < 1) :
    ∃ c : ℝ, c > 0 ∧ ∀ (n : ℕ) (z : Fin n → ℂ), (∀ i, z i ∈ F) →
      (Nat.card (ConnectedComponents ↥(sublevelSet z)) : ℝ) ≤ (1 - c) * n := by
  sorry

end Erdos1042
