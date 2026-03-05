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
# Erdős Problem 561

*Reference:* [erdosproblems.com/561](https://www.erdosproblems.com/561)

Determine the two-color size Ramsey number for disjoint unions of stars. If
$F_1$ and $F_2$ are disjoint unions of stars with non-increasing degree sequences,
prove that $\hat{R}(F_1, F_2) = \sum \ell_k$ where each $\ell_k$ is the maximum of
$n_i + m_j - 1$ over pairs with $i + j = k$.

[BEFRS78] Burr, S. A., Erdős, P., Faudree, R. J., Rousseau, C. C., and Schelp, R. H.,
_Ramsey numbers for the pair sparse graph-path or cycle_, Trans. Amer. Math. Soc. (1978).
-/

open Finset

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

/-- The two-color size Ramsey number $\hat{R}(G_1, G_2)$: the minimum number of edges in
a graph $H$ such that for every 2-coloring of the edges of $H$, either color 1
contains a copy of $G_1$ or color 2 contains a copy of $G_2$. -/
noncomputable def twoColorSizeRamseyNumber {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) : ℕ :=
  sInf {m : ℕ | ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
    H.edgeSet.ncard = m ∧
    ∀ c : Fin n → Fin n → Bool,
      (∀ i j, c i j = c j i) →
      (∃ f : V₁ → Fin n, Function.Injective f ∧
        ∀ u v, G₁.Adj u v → H.Adj (f u) (f v) ∧ c (f u) (f v) = true) ∨
      (∃ f : V₂ → Fin n, Function.Injective f ∧
        ∀ u v, G₂.Adj u v → H.Adj (f u) (f v) ∧ c (f u) (f v) = false)}

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
    twoColorSizeRamseyNumber
      (disjointUnionStars s n)
      (disjointUnionStars t m) =
    Finset.sum (Finset.range (s + t - 1)) (lFun s t n m) := by
  sorry

end Erdos561
