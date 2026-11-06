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

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-!
# Augmentation ideal and integral dimension subgroups

For a commutative ring `k` and a group `G`, `MonoidAlgebra.augmentation k G : k[G] →ₐ[k] k` is
the augmentation map `g ↦ 1`, and `MonoidAlgebra.augmentationIdeal k G` is its kernel.

For a group `G`, `Group.dimensionSubgroup n G` is the `n`-th integral dimension subgroup
$D_n(G) = G \cap (1 + \Delta^n) = \{g \in G \mid g - 1 \in \Delta^n\}$, where $\Delta$ is the
augmentation ideal of the integral group ring $\mathbb{Z}[G]$.

The indexing follows the literature: `dimensionSubgroup 1 G = ⊤`, and
`dimensionSubgroup 0 G = ⊤` as well, since `Δ ^ 0` is the whole ring.

## References

* I. B. S. Passi, *Group rings and their augmentation ideals*, Lecture Notes in Math. 715,
  Springer, 1979.
* R. Mikhailov, I. B. S. Passi, *Lower central and dimension series of groups*, Lecture Notes in
  Math. 1952, Springer, 2009.
-/

namespace MonoidAlgebra

variable (k G : Type*) [CommRing k] [Group G]

/-- The augmentation map `k[G] → k`, sending every group element `g` to `1`. -/
noncomputable def augmentation : MonoidAlgebra k G →ₐ[k] k :=
  lift k k G 1

/-- The augmentation ideal of `k[G]`: the kernel of the augmentation map. -/
noncomputable def augmentationIdeal : Ideal (MonoidAlgebra k G) :=
  RingHom.ker (augmentation k G)

instance augmentationIdeal.isTwoSided : (augmentationIdeal k G).IsTwoSided :=
  inferInstanceAs (RingHom.ker (augmentation k G)).IsTwoSided

variable {k G}

@[simp]
theorem augmentation_of (g : G) : augmentation k G (of k G g) = 1 := by
  simp [augmentation]

theorem mem_augmentationIdeal {x : MonoidAlgebra k G} :
    x ∈ augmentationIdeal k G ↔ augmentation k G x = 0 :=
  RingHom.mem_ker

theorem of_sub_one_mem_augmentationIdeal (g : G) : of k G g - 1 ∈ augmentationIdeal k G := by
  rw [mem_augmentationIdeal, map_sub, augmentation_of, map_one, sub_self]

end MonoidAlgebra

namespace Group

open MonoidAlgebra

/-- The `n`-th integral dimension subgroup
$D_n(G) = \{g \in G \mid g - 1 \in \Delta^n\}$, where $\Delta$ is the augmentation ideal of
$\mathbb{Z}[G]$. -/
noncomputable def dimensionSubgroup (n : ℕ) (G : Type*) [Group G] : Subgroup G where
  carrier := {g | of ℤ G g - 1 ∈ augmentationIdeal ℤ G ^ n}
  one_mem' := by
    change of ℤ G 1 - 1 ∈ augmentationIdeal ℤ G ^ n
    rw [map_one, sub_self]
    exact zero_mem _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    have h : of ℤ G (a * b) - 1 = (of ℤ G a - 1) * of ℤ G b + (of ℤ G b - 1) := by
      rw [map_mul]; noncomm_ring
    rw [h]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    have hh : of ℤ G a * of ℤ G a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h : of ℤ G a⁻¹ - 1 = -((of ℤ G a - 1) * of ℤ G a⁻¹) := by
      rw [sub_mul, hh]; noncomm_ring
    rw [h]
    exact neg_mem (Ideal.mul_mem_right _ _ ha)

variable {G : Type*} [Group G]

theorem mem_dimensionSubgroup {n : ℕ} {g : G} :
    g ∈ dimensionSubgroup n G ↔ of ℤ G g - 1 ∈ augmentationIdeal ℤ G ^ n :=
  Iff.rfl

instance dimensionSubgroup.normal (n : ℕ) : (dimensionSubgroup n G).Normal where
  conj_mem g hg h := by
    rw [mem_dimensionSubgroup] at *
    have hh : of ℤ G h * of ℤ G h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have e : of ℤ G (h * g * h⁻¹) - 1 = of ℤ G h * (of ℤ G g - 1) * of ℤ G h⁻¹ := by
      rw [map_mul, map_mul, mul_sub, sub_mul, mul_one, hh]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hg)

@[simp]
theorem dimensionSubgroup_zero : dimensionSubgroup 0 G = ⊤ := by
  ext g
  simp [mem_dimensionSubgroup, Submodule.pow_zero, Ideal.one_eq_top]

@[simp]
theorem dimensionSubgroup_one : dimensionSubgroup 1 G = ⊤ := by
  ext g
  simp only [mem_dimensionSubgroup, Submodule.pow_one, Subgroup.mem_top, iff_true]
  exact of_sub_one_mem_augmentationIdeal g

/-- The dimension series is decreasing. -/
theorem dimensionSubgroup_antitone : Antitone (fun n ↦ dimensionSubgroup n G) :=
  fun _ _ hmn _ hg ↦ Ideal.pow_le_pow_right hmn hg

end Group
