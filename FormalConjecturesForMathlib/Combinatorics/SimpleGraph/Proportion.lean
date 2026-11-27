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

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-!
# Proportions of finite labelled graphs

The cardinal ratio of a graph family is its probability under the uniform distribution
on all simple graphs on the fixed finite vertex set, equivalently the binomial model
with edge probability one half.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Fraction of all labelled simple graphs satisfying a property. -/
noncomputable def proportion (P : SimpleGraph V → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / Fintype.card (SimpleGraph V)

theorem proportion_nonneg (P : SimpleGraph V → Prop) : 0 ≤ proportion P := by
  classical
  unfold proportion
  positivity

theorem proportion_le_one (P : SimpleGraph V → Prop) : proportion P ≤ 1 := by
  classical
  unfold proportion
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset (SimpleGraph V)) P)

@[simp] theorem proportion_true : proportion (fun _ : SimpleGraph V => True) = 1 := by
  classical
  simp [proportion, Fintype.card_ne_zero]

@[simp] theorem proportion_false : proportion (fun _ : SimpleGraph V => False) = 0 := by
  classical
  simp [proportion]

theorem proportion_mono {P Q : SimpleGraph V → Prop} (h : ∀ G, P G → Q G) :
    proportion P ≤ proportion Q := by
  classical
  unfold proportion
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show
      Finset.univ.filter P ⊆ Finset.univ.filter Q from fun G hG =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ G, h G (Finset.mem_filter.mp hG).2⟩)

theorem proportion_not (P : SimpleGraph V → Prop) :
    proportion (fun G => ¬ P G) = 1 - proportion P := by
  classical
  unfold proportion
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (SimpleGraph V))) P
  have hden : (Fintype.card (SimpleGraph V) : ℝ) ≠ 0 := by positivity
  apply (eq_sub_iff_add_eq).mpr
  field_simp
  norm_cast
  simp only [Finset.card_univ] at h
  rw [Nat.add_comm]
  convert h using 1
  congr 2
  ext G
  simp
theorem proportion_equiv (e : SimpleGraph V ≃ SimpleGraph W)
    (P : SimpleGraph W → Prop) : proportion (fun G => P (e G)) = proportion P := by
  classical
  have hcard : (Finset.univ.filter (fun G => P (e G))).card =
      (Finset.univ.filter P).card := by
    simpa only [← Fintype.card_subtype] using
      Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))
  simp only [proportion, hcard, Fintype.card_congr e]

/-- Relabelling vertices preserves proportions. -/
theorem proportion_relabel (e : V ≃ W) (P : SimpleGraph W → Prop) :
    proportion (fun G => P (e.simpleGraph G)) = proportion P :=
  proportion_equiv e.simpleGraph P

end SimpleGraph
