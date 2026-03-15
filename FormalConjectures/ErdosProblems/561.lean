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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SizeRamsey

/-!
# Erdős Problem 561

*Reference:* [erdosproblems.com/561](https://www.erdosproblems.com/561)

Determine the two-color size Ramsey number for disjoint unions of stars. If
$F_1$ and $F_2$ are disjoint unions of stars with non-increasing degree sequences,
prove that $\hat{R}(F_1, F_2) = \sum \ell_k$ where each $\ell_k$ is the maximum of
$n_i + m_j - 1$ over pairs with $i + j = k$.

[BEFRS78] proved the special case where all $n_i$ are identical and all $m_j$ are
identical. The general conjecture remains open.

[BEFRS78] Burr, S. A., Erdős, P., Faudree, R. J., Rousseau, C. C., and Schelp, R. H.,
_Ramsey-minimal graphs for multiple copies_, Nederl. Akad. Wetensch. Indag. Math. (1978),
187-195.

[GySc02] Győri, E., Schelp, R. H., _Two-edge colorings of graphs with bounded degree in
both colors_, Discrete Math. (2002), 105-110.

[DJKR25] Davoodi, A., Javadi, R., Kamranian, A., Raeisi, G., _On a conjecture of Erdős
on size Ramsey number of star forests_, Ars Math. Contemp. (2025), Paper No. 9, 10 pages.
-/

open Finset SimpleGraph

namespace Erdos561

/-- Disjoint union of star graphs $K_{1,\deg(0)} \cup \cdots \cup K_{1,\deg(s-1)}$.
Vertex $\langle i, j \rangle$ belongs to the $i$-th star; $j = 0$ is the center. -/
def disjointUnionStars (s : ℕ) (deg : Fin s → ℕ) :
    SimpleGraph (Σ i : Fin s, Fin (deg i + 1)) where
  Adj x y := x.1 = y.1 ∧ ((x.2.val = 0 ∧ y.2.val ≠ 0) ∨ (x.2.val ≠ 0 ∧ y.2.val = 0))
  symm {_x} {_y} := fun ⟨heq, h⟩ =>
    ⟨heq.symm, h.elim (fun ⟨a, b⟩ => Or.inr ⟨b, a⟩) (fun ⟨a, b⟩ => Or.inl ⟨b, a⟩)⟩
  loopless _x := fun ⟨_, h⟩ =>
    h.elim (fun ⟨a, b⟩ => b a) (fun ⟨a, b⟩ => a b)

/-- $\ell_k = \max\{n_i + m_j - 1 : i + j = k\}$ for $0$-indexed $i < s$, $j < t$.
Returns $0$ when no valid $(i, j)$ pair exists with $i + j = k$. -/
def lFun (s t : ℕ) (n : Fin s → ℕ) (m : Fin t → ℕ) (k : ℕ) : ℕ :=
  (Finset.filter (fun p : Fin s × Fin t => p.1.val + p.2.val = k) Finset.univ).sup
    (fun p => n p.1 + m p.2 - 1)

/--
Erdős Problem 561 [BEFRS78]:

Let $\hat{R}(F_1, F_2)$ denote the two-color size Ramsey number. Let $F_1$ and $F_2$ be
disjoint unions of stars:
$$F_1 = K_{1,n_0} \cup \cdots \cup K_{1,n_{s-1}} \quad \text{with} \quad n_0 \geq \cdots \geq n_{s-1} \geq 1$$
$$F_2 = K_{1,m_0} \cup \cdots \cup K_{1,m_{t-1}} \quad \text{with} \quad m_0 \geq \cdots \geq m_{t-1} \geq 1$$

Then $\hat{R}(F_1, F_2) = \sum_{k=0}^{s+t-2} \ell_k$ where
$\ell_k = \max\{n_i + m_j - 1 : i + j = k\}$.
-/
@[category research open, AMS 5]
theorem erdos_561
    (s t : ℕ) (hs : s ≥ 1) (ht : t ≥ 1)
    (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hn_pos : ∀ i, n i ≥ 1)
    (hm_pos : ∀ j, m j ≥ 1)
    (hn_mono : ∀ i₁ i₂ : Fin s, i₁ ≤ i₂ → n i₂ ≤ n i₁)
    (hm_mono : ∀ j₁ j₂ : Fin t, j₁ ≤ j₂ → m j₂ ≤ m j₁) :
    sizeRamsey
      (disjointUnionStars s n)
      (disjointUnionStars t m) =
    Finset.sum (Finset.range (s + t - 1)) (lFun s t n m) := by
  sorry

/--
Erdős Problem 561, special case [BEFRS78]:

When all stars in $F_1$ have the same degree $n$ and all stars in $F_2$ have the same
degree $m$, the size Ramsey number $\hat{R}(F_1, F_2)$ equals the predicted formula.
This was proved by Burr, Erdős, Faudree, Rousseau, and Schelp.
-/
@[category research solved, AMS 5]
theorem erdos_561_identical_stars
    (s t : ℕ) (hs : s ≥ 1) (ht : t ≥ 1)
    (n_val m_val : ℕ) (hn_pos : n_val ≥ 1) (hm_pos : m_val ≥ 1) :
    sizeRamsey
      (disjointUnionStars s (fun _ => n_val))
      (disjointUnionStars t (fun _ => m_val)) =
    Finset.sum (Finset.range (s + t - 1))
      (lFun s t (fun _ => n_val) (fun _ => m_val)) := by
  sorry

end Erdos561
