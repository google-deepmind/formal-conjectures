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
import Mathlib.Data.Fin.Basic

variable {α : Type*} {𝒜 ℬ : Set (Set α)} {m n : ℕ}

variable (𝒜 n) in
def HasVCNDimAtMost : Prop :=
  ∀ (x : Fin (n + 1) → α) (y : Set (Fin (n + 1)) → Set α), (∀ s, y s ∈ 𝒜) →
    ∃ i s, ¬ x i ∈ y s ↔ i ∈ s

lemma HasVCDimAtMost.anti (h𝒜ℬ : 𝒜 ≤ ℬ) (hℬ : HasVCDimAtMost ℬ n) : HasVCDimAtMost 𝒜 n :=
  fun _x _y hy ↦ hℬ _ _ fun _s ↦ h𝒜ℬ <| hy _

lemma HasVCDimAtMost.mono (hmn : m ≤ n) (hm : HasVCDimAtMost 𝒜 m) : HasVCDimAtMost 𝒜 n := by
  rintro x y hy
  replace hmn : m + 1 ≤ n + 1 := by omega
  obtain ⟨i, s, his⟩ := hm (x ∘ Fin.castLE hmn) (y ∘ Set.image (Fin.castLE hmn)) (by simp [hy])
  exact ⟨Fin.castLE hmn i, Fin.castLE hmn '' s, by simp_all⟩

@[simp] lemma HasVCDimAtMost.empty : HasVCDimAtMost (∅ : Set (Set α)) n := by simp [HasVCDimAtMost]
