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

import FormalConjecturesUtil

/-!
# Erdős Problem 896

*References:*
- [erdosproblems.com/896](https://www.erdosproblems.com/896)
- [Fo08] Ford, Kevin, *The distribution of integers with a divisor in a given interval*. Ann. of
  Math. (2) (2008), 367-433.
-/

open Filter Asymptotics Finset
open scoped Topology

namespace Erdos896

/--
$F(A,B)$ counts the number of $m$ such that $m=ab$ has exactly one solution with $a\in A$ and
$b\in B$.
-/
def F (A B : Finset ℕ) : ℕ :=
  (uniqueMulProducts A B).card

/--
The maximum of $F(A,B)$ as $A,B$ range over all subsets of $\{1,\ldots,N\}$.
-/
def maxF (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.product (Icc 1 N).powerset).sup fun p => F p.1 p.2

/-- Ford's constant $\delta=1-\frac{1+\log\log 2}{\log 2}\approx 0.086$. -/
noncomputable def fordDelta : ℝ :=
  1 - (1 + Real.log (Real.log 2)) / Real.log 2

/--
Estimate the maximum of $F(A,B)$ as $A,B$ range over all subsets of $\{1,\ldots,N\}$, where
$F(A,B)$ counts the number of $m$ such that $m=ab$ has exactly one solution (with $a\in A$ and
$b\in B$).

The order of magnitude of $F(A,B)$ is now known:
$$F(A,B)\asymp \frac{N^2}{(\log N)^\delta(\log\log N)^{3/2}}$$
where $\delta=1-\frac{1+\log\log 2}{\log 2}\approx 0.086$. The upper bound is an immediate
consequence of the bound on the size of $\{1,\ldots,N\}\cdot\{1,\ldots,N\}$ given by Ford [Fo08].
The lower bound was proved by GPT-5.5 Pro (prompted by Chojecki), using a similar result from
[Fo08]; the proof is sketched in the comments.
-/
@[category research solved, AMS 11]
theorem erdos_896 :
    (fun N : ℕ => (maxF N : ℝ)) =Θ[atTop]
      fun N : ℕ =>
        (N : ℝ) ^ 2 / ((Real.log N) ^ fordDelta * (Real.log (Real.log N)) ^ ((3 : ℝ) / 2)) := by
  sorry

/-- $F(\{2\},\{3\})$ counts the unique product $6$. -/
@[category test, AMS 11]
theorem erdos_896.variants.F_singleton : F {2} {3} = 1 := by
  simp [F, uniqueMulProducts_singleton]

/-- $F(A,\emptyset)=F(\emptyset,B)=0$ for any finite $A,B$. -/
@[category test, AMS 11]
theorem erdos_896.variants.F_empty (A B : Finset ℕ) : F A ∅ = 0 ∧ F ∅ B = 0 := by
  simp [F]

/-- Products $1,2,4$ from $\{1,2\}\times\{1,2\}$; only $1$ and $4$ are unique. -/
@[category test, AMS 11]
theorem erdos_896.variants.F_two_representations : F {1, 2} {1, 2} = 2 := by
  decide

/-- `F(A,B)` cannot exceed `|A|·|B|`. -/
@[category test, AMS 11]
theorem erdos_896.variants.F_le_card_mul (A B : Finset ℕ) :
    F A B ≤ A.card * B.card := by
  simpa [F] using card_uniqueMulProducts_le A B

/-- `F` is symmetric in its two arguments. -/
@[category API, AMS 11]
theorem erdos_896.variants.F_comm (A B : Finset ℕ) : F A B = F B A := by
  simp [F, card_uniqueMulProducts_comm]

/-- `maxF N` is at most `N²` (each factor set has size ≤ `N`). -/
@[category API, AMS 11]
theorem erdos_896.variants.maxF_le_sq (N : ℕ) : maxF N ≤ N ^ 2 := by
  classical
  refine Finset.sup_le fun p hp ↦ ?_
  have hp' := mem_product.mp hp
  have hA : p.1 ⊆ Icc 1 N := mem_powerset.mp hp'.1
  have hB : p.2 ⊆ Icc 1 N := mem_powerset.mp hp'.2
  have hcard : (Icc 1 N).card = N := by simp [Nat.card_Icc]
  simpa [F, hcard, sq] using card_uniqueMulProducts_le_sq_of_subset hA hB

/-- `maxF` is positive for `N ≥ 1`. -/
@[category API, AMS 11]
theorem erdos_896.variants.maxF_pos {N : ℕ} (hN : 1 ≤ N) : 0 < maxF N := by
  classical
  have hmem :
      (({1} : Finset ℕ), ({1} : Finset ℕ)) ∈
        (Icc 1 N).powerset.product (Icc 1 N).powerset := by
    simp [mem_product, mem_powerset, hN]
  have hle : 1 ≤ maxF N := by
    have : F ({1} : Finset ℕ) {1} = 1 := by
      rw [F, uniqueMulProducts_singleton, card_singleton]
    rw [← this]
    exact le_sup (f := fun p : Finset ℕ × Finset ℕ ↦ F p.1 p.2) hmem
  exact Nat.succ_le_iff.mp hle


/-- `F({1}, B) = #B`. -/
@[category API, AMS 11]
theorem erdos_896.variants.F_one_left (B : Finset ℕ) : F {1} B = B.card := by
  simp [F]

/-- `F(A, {1}) = #A`. -/
@[category API, AMS 11]
theorem erdos_896.variants.F_one_right (A : Finset ℕ) : F A {1} = A.card := by
  simp [F]

/-- `maxF` is monotone in `N`. -/
@[category API, AMS 11]
theorem erdos_896.variants.maxF_mono {M N : ℕ} (h : M ≤ N) : maxF M ≤ maxF N := by
  classical
  refine Finset.sup_le fun p hp ↦ ?_
  have hp' := mem_product.mp hp
  have hA : p.1 ⊆ Icc 1 M := mem_powerset.mp hp'.1
  have hB : p.2 ⊆ Icc 1 M := mem_powerset.mp hp'.2
  have hAN : p.1 ⊆ Icc 1 N := hA.trans (Icc_subset_Icc_right h)
  have hBN : p.2 ⊆ Icc 1 N := hB.trans (Icc_subset_Icc_right h)
  have hmem :
      (p.1, p.2) ∈ (Icc 1 N).powerset.product (Icc 1 N).powerset := by
    simp [mem_product, mem_powerset, hAN, hBN]
  exact le_sup (f := fun q : Finset ℕ × Finset ℕ ↦ F q.1 q.2) hmem

/-- `maxF 0 = 0`. -/
@[category test, AMS 11]
theorem erdos_896.variants.maxF_zero : maxF 0 = 0 := by
  classical
  have hI : Icc 1 0 = (∅ : Finset ℕ) := by simp
  simp [maxF, hI]

/-- `maxF 1 = 1`. -/
@[category test, AMS 11]
theorem erdos_896.variants.maxF_one : maxF 1 = 1 := by
  refine le_antisymm ?_ ?_
  · simpa using maxF_le_sq 1
  · exact Nat.succ_le_iff.mp (maxF_pos (Nat.le_refl 1))


end Erdos896
