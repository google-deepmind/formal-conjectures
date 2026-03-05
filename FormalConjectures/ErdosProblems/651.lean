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
# Erdős Problem 651

*Reference:* [erdosproblems.com/651](https://www.erdosproblems.com/651)

Let $f_k(n)$ denote the smallest integer such that any $f_k(n)$ points in general
position in $\mathbb{R}^k$ contain $n$ points forming the vertices of a convex polytope.
Erdős conjectured that $f_k(n)$ grows at least exponentially in $n$ for each fixed
$k \geq 2$. This was disproved for $k \geq 3$ by Pohoata and Zakharov, who showed
$f_3(n) \leq 2^{o(n)}$.

[Er97e] Erdős, P., *Some of my favourite problems which recently have been solved*, 1997.

[PoZa22] Pohoata, C. and Zakharov, D., *Convex polytopes from fewer points*, 2022.
-/

namespace Erdos651

/-- A finite point set in $\mathbb{R}^k$ is in general position if any $k+1$ distinct
points are affinely independent (no $k+1$ points lie on a common hyperplane). -/
def InGeneralPositionRk (k : ℕ) (P : Finset (EuclideanSpace ℝ (Fin k))) : Prop :=
  ∀ f : Fin (k + 1) → EuclideanSpace ℝ (Fin k),
    (∀ i, f i ∈ P) → Function.Injective f →
    AffineIndependent ℝ f

/-- A finite point set in $\mathbb{R}^k$ is in convex position if no point lies in the
convex hull of the remaining points (the points are the vertices of a convex polytope). -/
def InConvexPositionRk (k : ℕ) (S : Finset (EuclideanSpace ℝ (Fin k))) : Prop :=
  ∀ p ∈ S, p ∉ convexHull ℝ (↑(S.erase p) : Set (EuclideanSpace ℝ (Fin k)))

/-- $f_k(n)$: the smallest integer $m$ such that any $m$ points in general position
in $\mathbb{R}^k$ contain $n$ points in convex position (forming the vertices of a
convex polytope). -/
noncomputable def fk (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ P : Finset (EuclideanSpace ℝ (Fin k)),
    P.card = m →
    InGeneralPositionRk k P →
    ∃ Q : Finset (EuclideanSpace ℝ (Fin k)),
      Q ⊆ P ∧ Q.card = n ∧ InConvexPositionRk k Q}

/--
Erdős Problem 651 [Er97e]:

Let $f_k(n)$ denote the smallest integer such that any $f_k(n)$ points in general
position in $\mathbb{R}^k$ contain $n$ points forming the vertices of a convex polytope.
The conjecture asks whether $f_k(n)$ grows at least exponentially in $n$ for
each fixed $k \geq 2$, i.e., whether there exists $c_k > 0$ such that
$$f_k(n) > (1 + c_k)^n.$$

DISPROVED for $k \geq 3$: Pohoata and Zakharov [PoZa22] proved $f_3(n) \leq 2^{o(n)}$.
-/
@[category research solved, AMS 5 52]
theorem erdos_651 : answer(False) ↔
    ∀ (k : ℕ), k ≥ 2 → ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (fk k n : ℝ) > (1 + c) ^ n := by
  sorry

end Erdos651
