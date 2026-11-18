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

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Numerical semigroups

An additive submonoid $S \le \mathbb{N}$ with finite complement $\mathbb{N} \setminus S$ is a
*numerical semigroup*. This file defines the predicate `AddSubmonoid.IsNumericalSemigroup`, the
conductor $c(S)$, and the embedding dimension $e(S)$.

*References:*
- [Wikipedia, Numerical semigroup](https://en.wikipedia.org/wiki/Numerical_semigroup)
- R. Fröberg, C. Gottlieb, and R. Häggkvist, *On numerical semigroups*, Semigroup Forum **35**
  (1987), no. 1, 63–83.
-/

namespace AddSubmonoid

/-- An additive submonoid `S : AddSubmonoid ℕ` is a numerical semigroup when `ℕ \ S` is finite. -/
def IsNumericalSemigroup (S : AddSubmonoid ℕ) : Prop :=
  (S : Set ℕ)ᶜ.Finite

/-- Conductor $c(S) = \min\{c \in \mathbb{N} : \forall m \ge c,\, m \in S\}$. -/
noncomputable def conductor (S : AddSubmonoid ℕ) : ℕ :=
  sInf {c : ℕ | ∀ m : ℕ, c ≤ m → m ∈ S}

/-- Embedding dimension $e(S) = |S_{>0} \setminus (S_{>0} + S_{>0})|$, counting minimal positive
generators of $S$. -/
noncomputable def embeddingDim (S : AddSubmonoid ℕ) : ℕ :=
  {x : ℕ | 0 < x ∧ x ∈ S ∧ ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ∈ S ∧ b ∈ S ∧ x = a + b}.ncard

/-- Every integer $m \ge \operatorname{conductor}(S)$ belongs to a numerical semigroup $S$. -/
theorem IsNumericalSemigroup.mem_of_conductor_le {S : AddSubmonoid ℕ}
    (hS : S.IsNumericalSemigroup) {m : ℕ} (hm : S.conductor ≤ m) : m ∈ S := by
  let A : Set ℕ := {c : ℕ | ∀ k : ℕ, c ≤ k → k ∈ S}
  have hA_ne : A.Nonempty := by
    refine ⟨hS.toFinset.sup id + 1, fun k hk => ?_⟩
    by_contra hkS
    have hkF : k ∈ hS.toFinset := hS.mem_toFinset.mpr hkS
    have hle : k ≤ hS.toFinset.sup id := Finset.le_sup (f := id) hkF
    omega
  exact Nat.sInf_mem hA_ne m hm

@[simp]
theorem isNumericalSemigroup_top : (⊤ : AddSubmonoid ℕ).IsNumericalSemigroup := by
  simp [IsNumericalSemigroup]

@[simp]
theorem conductor_top : (⊤ : AddSubmonoid ℕ).conductor = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl (fun _ _ => trivial))

@[simp]
theorem embeddingDim_top : (⊤ : AddSubmonoid ℕ).embeddingDim = 1 := by
  unfold embeddingDim
  have hset : {x : ℕ | 0 < x ∧ x ∈ (⊤ : AddSubmonoid ℕ) ∧
      ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
        a ∈ (⊤ : AddSubmonoid ℕ) ∧ b ∈ (⊤ : AddSubmonoid ℕ) ∧ x = a + b} = {1} := by
    ext x
    simp only [Set.mem_ofPred_eq, AddSubmonoid.mem_top, true_and, Set.mem_singleton_iff]
    refine ⟨fun ⟨hx, hmin⟩ => ?_, ?_⟩
    · by_contra hx1
      exact hmin ⟨1, x - 1, by omega, by omega, by omega⟩
    · rintro rfl
      exact ⟨by omega, fun ⟨a, b, ha, hb, hsum⟩ => by omega⟩
  rw [hset, Set.ncard_singleton]

end AddSubmonoid
