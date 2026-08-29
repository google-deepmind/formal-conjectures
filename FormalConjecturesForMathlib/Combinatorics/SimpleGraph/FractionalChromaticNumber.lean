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

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-!
# The fractional chromatic number

A **fractional colouring** of a finite graph `G` assigns a nonnegative real weight to every
independent set so that every vertex receives total weight at least `1`; the **fractional
chromatic number** `χ_f(G)` is the infimum of the total weights of fractional colourings. This is
the linear-programming relaxation of the chromatic number. Mathlib (as of 2026-08) has no such
notion.

We prove that the singleton weighting is a fractional colouring, so that `χ_f(G) ≤ |V|`, and
that `χ_f(G) ≥ 0`.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- `w` is a **fractional colouring** of `G`: nonnegative weights supported on independent sets,
covering every vertex with total weight at least `1`. -/
structure IsFractionalColoring (w : Finset V → ℝ) : Prop where
  nonneg : ∀ S, 0 ≤ w S
  indep : ∀ S, w S ≠ 0 → G.IsIndepSet (S : Set V)
  cover : ∀ v, 1 ≤ ∑ S ∈ (Finset.univ : Finset (Finset V)).filter (fun S => v ∈ S), w S

/-- The set of total weights of fractional colourings of `G`. -/
def fractionalColoringWeights : Set ℝ :=
  {t | ∃ w : Finset V → ℝ, G.IsFractionalColoring w ∧ ∑ S, w S = t}

/-- The **fractional chromatic number** `χ_f(G)`. -/
noncomputable def fractionalChromaticNumber : ℝ :=
  sInf (fractionalColoringWeights G)

/-- The weighting giving weight `1` to every singleton (and `0` elsewhere). -/
def singletonWeights : Finset V → ℝ := fun S => if S.card = 1 then 1 else 0

/-- The singleton weighting is a fractional colouring. -/
theorem isFractionalColoring_singletonWeights : G.IsFractionalColoring singletonWeights where
  nonneg S := by unfold singletonWeights; split_ifs <;> norm_num
  indep S hS := by
    unfold singletonWeights at hS
    split_ifs at hS with h
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
      intro x hx y hy hxy
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
      exact absurd (hx.trans hy.symm) hxy
    · exact absurd rfl hS
  cover v := by
    have hmem : {v} ∈ (Finset.univ : Finset (Finset V)).filter (fun S => v ∈ S) := by simp
    calc (1 : ℝ) = singletonWeights {v} := by simp [singletonWeights]
      _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset V)).filter (fun S => v ∈ S), singletonWeights S :=
          Finset.single_le_sum (fun S _ => by unfold singletonWeights; split_ifs <;> norm_num) hmem

/-- The total weight of the singleton weighting is `|V|`. -/
theorem sum_singletonWeights : ∑ S : Finset V, singletonWeights S = Fintype.card V := by
  unfold singletonWeights
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [← Finset.card_univ,
    ← Finset.card_map ⟨fun v => ({v} : Finset V), fun _ _ h => Finset.singleton_injective h⟩]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.card_eq_one]
  constructor <;> rintro ⟨a, ha⟩ <;> exact ⟨a, ha.symm⟩

/-- There is at least one fractional colouring. -/
theorem fractionalColoringWeights_nonempty : (fractionalColoringWeights G).Nonempty :=
  ⟨_, singletonWeights, G.isFractionalColoring_singletonWeights, rfl⟩

/-- Total weights of fractional colourings are nonnegative. -/
theorem fractionalColoringWeights_nonneg {t : ℝ} (ht : t ∈ fractionalColoringWeights G) : 0 ≤ t := by
  obtain ⟨w, hw, rfl⟩ := ht
  exact Finset.sum_nonneg fun S _ => hw.nonneg S

/-- `χ_f(G) ≥ 0`. -/
theorem fractionalChromaticNumber_nonneg : 0 ≤ G.fractionalChromaticNumber :=
  Real.sInf_nonneg fun _ ht => G.fractionalColoringWeights_nonneg ht

/-- The trivial upper bound `χ_f(G) ≤ |V|`. -/
theorem fractionalChromaticNumber_le_card : G.fractionalChromaticNumber ≤ Fintype.card V := by
  refine csInf_le ⟨0, fun _ ht => G.fractionalColoringWeights_nonneg ht⟩ ?_
  exact ⟨singletonWeights, G.isFractionalColoring_singletonWeights, sum_singletonWeights⟩

end SimpleGraph
