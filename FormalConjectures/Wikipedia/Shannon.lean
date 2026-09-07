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

import FormalConjecturesUtil

/-!
# Shannon capacity of a graph

The *Shannon capacity* of a graph $G$ is
$$\Theta(G) = \sup_{n} \sqrt[n]{\alpha(G^{\boxtimes n})},$$
where $\alpha$ denotes the independence number and $G^{\boxtimes n}$ the $n$-th power of $G$
with respect to the strong product $\boxtimes$. It measures the effective alphabet size of a
noisy channel whose confusability graph is $G$.

Lovász showed that $\Theta(C_5) = \sqrt 5$, but the Shannon capacity of $C_7$ is unknown: it is
not even known whether it agrees with the Lovász number
$\vartheta(C_7) = \frac{7\cos(\pi/7)}{1 + \cos(\pi/7)}$, which is an upper bound for it.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Shannon_capacity_of_a_graph)
- [Lo79] Lovász, László, On the Shannon capacity of a graph. IEEE Trans. Inform. Theory (1979),
  1--7.
- [PoSc19] Polak, Sven C. and Schrijver, Alexander, New lower bound on the Shannon capacity of
  $C_7$ from circular graphs. Inform. Process. Lett. (2019), 37--40.
  [arXiv:1808.07438](https://arxiv.org/abs/1808.07438)
-/

universe u

variable {α β : Type u}

namespace SimpleGraph

/-- Tensor product of simple graphs. `(a₁, b₁)` is adjacent to `(a₂, b₂)` if `a₁` is adjacent to
`a₂` and `b₁` is adjacent to `b₂`.

Replace once https://github.com/leanprover-community/mathlib4/pull/43170 lands.-/
def tensorProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm.symm x y h := by rwa [adj_comm G, adj_comm H]

/-- Strong product of simple graphs. It relates `(a₁, b₁)` and `(a₂, b₂)` if `a₁` and `a₂` are
equal or adjacent in `G`, and `b₁` and `b₂` are equal or adjacent in `H` (and `(a₁, b₁)` and
`(a₂, b₂)` are distinct).

Replace once https://github.com/leanprover-community/mathlib4/pull/43170 lands.-/
def strongProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) :=
  boxProd G H ⊔ tensorProd G H

infixl:70 " ⊠ " => strongProd

/-- The power of a simple graph w. r. t. the strong product. -/
def strongPow (G : SimpleGraph α) : (n : ℕ) → SimpleGraph (Fin n → α)
  | 0 => completeGraph _
  | n + 1 => (Fin.succFunEquiv α n).symm.simpleGraph <| (strongPow G n) ⊠ G

/-- The Shannon capacity $\Theta(G) = \sup_n \sqrt[n]{\alpha(G^{\boxtimes n})}$ of a graph. -/
noncomputable def shannonCapacity (G : SimpleGraph α) : ℝ :=
  sSup {(↑α(G.strongPow n) : ℝ) ^ (↑n : ℝ)⁻¹ | n > 0}

-- easy, but needs more API for `SimpleGraph.indepNum`
@[category API, AMS 5 94]
lemma bddAbove_shannonCapacity [Finite α] (G : SimpleGraph α) :
    BddAbove {(↑α(G.strongPow n) : ℝ) ^ (↑n : ℝ)⁻¹ | n > 0} := by
  sorry

@[category API, AMS 5 94]
theorem indepNum_strongPow_le_shannonCapacity [Finite α] (G : SimpleGraph α) {n : ℕ} (hn : 0 < n):
    (↑α(G.strongPow n) : ℝ) ^ (↑n : ℝ)⁻¹ ≤ shannonCapacity G := by
  apply le_csSup (bddAbove_shannonCapacity G)
  grind

-- easy, but needs more API for `SimpleGraph.indepNum`
@[category API, AMS 5 94]
theorem indepNum_le_shannonCapacity [Finite α] (G : SimpleGraph α) :
    ↑α(G) ≤ shannonCapacity G := by
  sorry

/--
The Shannon capacity of the $5$-cycle is $\sqrt 5$.

This was proved by Lovász [Lo79], who introduced the Lovász number $\vartheta$ and showed
$\Theta(G) \le \vartheta(G)$ together with $\vartheta(C_5) = \sqrt 5 = \alpha(C_5^{\boxtimes 2})^{1/2}$.
-/
@[category research solved, AMS 5 94]
theorem shannonCapacityC5 : shannonCapacity (cycleGraph 5) = √5 := by sorry

/--
Is the Shannon capacity of the $7$-cycle equal to its Lovász number
$\vartheta(C_7) = \frac{7\cos(\pi/7)}{1 + \cos(\pi/7)}$?
-/
@[category research open, AMS 5 94]
theorem shannonCapacityC7 : answer(sorry) ↔
    shannonCapacity (cycleGraph 7) =
      (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7)) := by
  sorry

/-- A lower bound for the independece number of $C_7^5$ given by [PoSc19]. -/
@[category research solved, AMS 5 94]
theorem threesixseven_le_indepNum_pow_five : 367 ≤ indepNum (strongPow (cycleGraph 7) 5) := by
  sorry

/-- A lower bound for the shannon capacity of $C_7$ given by [PoSc19]. -/
@[category research solved, AMS 5 94]
theorem root_367_le_shannonCapacityC7 : (367 : ℝ) ^ (5 : ℝ)⁻¹ ≤ shannonCapacity (cycleGraph 7) := by
  apply le_trans ?_ (indepNum_strongPow_le_shannonCapacity (cycleGraph 7) (n := 5) (by norm_num))
  simp only [Nat.cast_ofNat]
  gcongr
  have (a b : ℕ) : a ≤ b ↔ (a : ℝ) ≤ b := by exact Iff.symm Nat.cast_le
  convert (Nat.cast_le (α := ℝ)).mpr threesixseven_le_indepNum_pow_five
  · rfl
  · rfl

end SimpleGraph
