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

/-!
# Erdős Problem 530

*References:*
- [erdosproblems.com/530](https://www.erdosproblems.com/530)
- [Ri69] Riddell, J., _On sets of numbers containing no $l$ terms in arithmetic
  progression_. Nieuw Arch. Wisk. (3) (1969), 204–209.
- [KSS75] Komlós, J., Sulyok, M., and Szemerédi, E., _Linear problems in
  combinatorial number theory_. Acta Math. Acad. Sci. Hungar. (1975), 113–121.
- [BR26] Bailleul, Alexandre and Riblet, Robin, _On the largest Sidon subset in
  a finite subset of $\mathbb R^N$_.
  [arXiv:2605.03181](https://arxiv.org/abs/2605.03181)
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace Erdos530

/-- `A` contains a Sidon subset of cardinality exactly `k`. -/
def HasSidonSubsetOfCard (A : Finset ℝ) (k : ℕ) : Prop :=
  ∃ S : Finset ℝ, S ⊆ A ∧ IsSidon (S : Set ℝ) ∧ S.card = k

/-- Every $N$-element finite set of reals contains a Sidon subset of size $k$. -/
def UniformSidonSubsetSize (N k : ℕ) : Prop :=
  ∀ A : Finset ℝ, A.card = N → HasSidonSubsetOfCard A k

/-- The largest Sidon subset size guaranteed in every $N$-element real set. -/
noncomputable def ell (N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (UniformSidonSubsetSize N) N

local notation "ℓ" => ell

@[category API, AMS 5 11]
theorem uniformSidonSubsetSize_zero (N : ℕ) : UniformSidonSubsetSize N 0 := by
  intro A _
  exact ⟨∅, Finset.empty_subset A, by simp [IsSidon], by simp⟩

@[category API, AMS 5 11]
theorem UniformSidonSubsetSize.mono {N k m : ℕ} (h : UniformSidonSubsetSize N k)
    (hm : m ≤ k) : UniformSidonSubsetSize N m := by
  classical
  intro A hA
  obtain ⟨S, hSA, hS, hcard⟩ := h A hA
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (hcard ▸ hm)
  exact ⟨T, hTS.trans hSA, Set.IsSidon.subset hS (Finset.coe_subset.mpr hTS), hT⟩

@[category API, AMS 5 11]
theorem UniformSidonSubsetSize.le {N k : ℕ} (h : UniformSidonSubsetSize N k) : k ≤ N := by
  classical
  let A : Finset ℝ := (Finset.range N).map ⟨fun n : ℕ => (n : ℝ), Nat.cast_injective⟩
  have hA : A.card = N := by simp [A]
  obtain ⟨S, hSA, _, hS⟩ := h A hA
  rw [← hS, ← hA]
  exact Finset.card_le_card hSA

@[category API, AMS 5 11]
theorem ell_le (N : ℕ) : ℓ N ≤ N := by
  classical
  exact Nat.findGreatest_le N

@[category API, AMS 5 11]
theorem ell_spec (N : ℕ) : UniformSidonSubsetSize N (ℓ N) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le N) (uniformSidonSubsetSize_zero N)

/-- `ell` is the greatest size uniformly guaranteed over all ambient real sets. -/
@[category API, AMS 5 11]
theorem uniformSidonSubsetSize_iff {N k : ℕ} : UniformSidonSubsetSize N k ↔ k ≤ ℓ N := by
  classical
  constructor
  · intro h
    exact Nat.le_findGreatest h.le h
  · exact (ell_spec N).mono

@[simp, category API, AMS 5 11]
theorem ell_zero : ℓ 0 = 0 := Nat.eq_zero_of_le_zero (ell_le 0)

@[simp, category API, AMS 5 11]
theorem ell_one : ℓ 1 = 1 := by
  classical
  apply le_antisymm (ell_le 1)
  apply uniformSidonSubsetSize_iff.mp
  intro A hA
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA
  exact ⟨{a}, Finset.Subset.refl _, by simp [IsSidon], by simp⟩

/-- Let $\ell(N)$ be maximal such that in any finite set $A\subset\mathbb R$ of
size $N$ there exists a Sidon subset $S$ of size $\ell(N)$ (i.e. the only solutions
to $a+b=c+d$ in $S$ are the trivial ones). Determine the order of $\ell(N)$.

The lower bound was improved to $N^{1/2}\ll\ell(N)$ by Komlós, Sulyok, and
Szemerédi [KSS75]. Together with the interval upper bound this gives the order. -/
@[category research solved, AMS 5 11]
theorem erdos_530.parts.i :
    (fun N : ℕ => (ℓ N : ℝ)) =Θ[atTop] (fun N : ℕ => Real.sqrt N) := by
  sorry

/-- In particular, is it true that $\ell(N)\sim N^{1/2}$? -/
@[category research open, AMS 5 11]
theorem erdos_530.parts.ii : answer(sorry) ↔
    (fun N : ℕ => (ℓ N : ℝ)) ~[atTop] (fun N : ℕ => Real.sqrt N) := by
  sorry

/-- Bailleul and Riblet [BR26, Theorem 2.1] prove
$\ell(N)\geq(1/(3\sqrt3)+o(1))\sqrt N$. -/
@[category research solved, AMS 5 11]
theorem erdos_530.variants.bailleul_riblet :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (1 / (3 * Real.sqrt 3) - ε) * Real.sqrt N ≤ (ℓ N : ℝ) := by
  sorry

end Erdos530
