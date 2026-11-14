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
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SizeRamsey

/-!
# Erdős Problem 561

*References:*
- [erdosproblems.com/561](https://www.erdosproblems.com/561)
- [BEFRS78] Burr, S. A. and Erdős, P. and Faudree, R. J. and Rousseau, C. C. and Schelp, R. H.,
  Ramsey-minimal graphs for multiple copies. Nederl. Akad. Wetensch. Indag. Math. (1978), 187-195.
-/

@[expose] public section

namespace Erdos561

open SimpleGraph

/-- `F(s,n)` is the disjoint union of the stars $K_{1,n_i}$. The vertex $(i,0)$ is the center
of component $i$; its other $n_i$ vertices are leaves. -/
local notation "F(" s ", " n ")" =>
  fromRel (fun (u v : Σ i : Fin s, Fin (n i + 1)) ↦
    Sigma.fst u = Sigma.fst v ∧
      (Fin.val (Sigma.snd u) = 0 ∨ Fin.val (Sigma.snd v) = 0))

/--
Let $\hat{R}(G)$ denote the size Ramsey number, the minimal number of edges $m$ such that there
is a graph $H$ with $m$ edges such that in any $2$-colouring of the edges of $H$ there is a
monochromatic copy of $G$.

Let $F_1$ and $F_2$ be the union of stars. More precisely, let
$F_1=\cup_{i\leq s}K_{1,n_i}$ and $F_2=\cup_{j\leq t}K_{1,m_j}$ with
$n_1\geq\cdots\geq n_s\geq1$ and $m_1\geq\cdots\geq m_t\geq1$. Prove that
$$\hat{R}(F_1,F_2)=\sum_{2\leq k\leq s+t}l_k$$
where
$$l_k=\max\{n_i+m_j-1:i+j=k\}.$$

The unions are vertex-disjoint, and $s,t\geq1$. Lean indices start at zero, so the condition
$i+j=k$ is represented by $(i+1)+(j+1)=k$.
-/
@[category research open, AMS 5]
theorem erdos_561 :
    ∀ (s t : ℕ), 1 ≤ s → 1 ≤ t →
    ∀ (n : Fin s → ℕ) (m : Fin t → ℕ),
      Antitone n → Antitone m → (∀ i, 1 ≤ n i) → (∀ j, 1 ≤ m j) →
      sizeRamsey F(s, n) F(t, m) =
        ∑ k ∈ Finset.Icc 2 (s + t),
          ((Finset.univ : Finset (Fin s × Fin t)).filter
            (fun p ↦ (p.1.val + 1) + (p.2.val + 1) = k)).sup
              (fun p ↦ n p.1 + m p.2 - 1) := by
  sorry

end Erdos561
