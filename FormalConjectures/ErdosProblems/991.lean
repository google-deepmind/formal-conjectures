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
# Erdős Problem 991

*Reference:* [erdosproblems.com/991](https://www.erdosproblems.com/991)

Suppose $A = \{w_1, \ldots, w_n\} \subset S^2$ maximises $\prod_{i<j} |w_i - w_j|$ over all
possible sets of size $n$ (such sets are called Fekete points).

Is it true that
$$
  \max_C \left| |A \cap C| - \alpha_C \cdot n \right| = o(n),
$$
where the maximum is taken over all spherical caps $C$ and $\alpha_C$ is the area
of $C$ (normalised so that the entire sphere has area $1$)?

This was proved. Brauchart [Br08] showed $O(n^{3/4})$, and Marzo–Mas [MaMa21]
improved this to $O(n^{2/3})$ (Wolff obtained the same bound independently in
an unpublished manuscript).

See also: Erdős Problem 988.

[Br08] Brauchart, J. S., *Optimal logarithmic energy points on the unit sphere*,
Mathematics of Computation (2008), 1599–1613.

[MaMa21] Marzo, J. and Mas, A., *Discrepancy of minimal Riesz energy points*,
Constructive Approximation (2021), 473–506.
-/

open Classical Finset BigOperators
open scoped EuclideanGeometry

namespace Erdos991

/-- The product of all ordered pairwise distances $\prod_{i \neq j} \|w_i - w_j\|$ of a finite set
of points. This is the square of the product over unordered pairs $\prod_{i < j}$, so it has the
same maximizers. -/
noncomputable def pairwiseDistProd (P : Finset (ℝ³)) : ℝ :=
  ∏ p ∈ P.offDiag, ‖p.1 - p.2‖

/-- A finite set of points on $S^2$ maximises the pairwise distance product
among all sets of the same cardinality on $S^2$. -/
def IsMaxPairwiseDist (P : Finset (ℝ³)) : Prop :=
  (∀ p ∈ P, ‖p‖ = 1) ∧
  ∀ (Q : Finset (ℝ³)),
    (∀ q ∈ Q, ‖q‖ = 1) → Q.card = P.card →
    pairwiseDistProd Q ≤ pairwiseDistProd P

/--
Erdős Problem 991 [Er64b]:

If $A = \{w_1, \ldots, w_n\} \subset S^2$ are Fekete points (maximising the product of
pairwise distances), then the spherical cap discrepancy of $A$ is $o(n)$:
for every $\varepsilon > 0$, if $n$ is large enough and $P$ is any set of $n$ Fekete points,
then for every spherical cap $C(v,t) = \{x \in S^2 : \langle x,v \rangle \geq t\}$,
$$
  \left| |P \cap C(v,t)| - \frac{1-t}{2} \cdot n \right| \leq \varepsilon \cdot n.
$$

Here $\frac{1-t}{2}$ is the normalised surface area of the cap $C(v,t)$ on $S^2$.
-/
@[category research solved, AMS 31 52]
theorem erdos_991 :
    answer(True) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ (P : Finset (ℝ³)),
      IsMaxPairwiseDist P →
      P.card ≥ N₀ →
      ∀ (v : ℝ³) (t : ℝ),
        ‖v‖ = 1 → -1 ≤ t → t ≤ 1 →
        |((P.filter (fun x => @inner ℝ _ _ x v ≥ t)).card : ℝ) -
          (1 - t) / 2 * (P.card : ℝ)| ≤ ε * (P.card : ℝ) := by
  sorry

end Erdos991
