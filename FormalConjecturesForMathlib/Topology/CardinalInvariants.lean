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

public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Topology.Bases

/-!
# Cardinal invariants of topological spaces

This file defines networks of a topological space and two cardinal invariants:
the *density* `d(X)` and the *network weight* `nw(X)`.
-/

@[expose] public section

universe u

open Cardinal Set Topology

namespace TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A family `N` of subsets of a topological space `X` is a *network* for `X` if every open
subset of `X` is a union of members of `N`. Unlike the members of a topological basis, the members
of a network need not be open. -/
def IsNetwork (N : Set (Set X)) : Prop :=
  ∀ ⦃U : Set X⦄, IsOpen U → ∀ x ∈ U, ∃ n ∈ N, x ∈ n ∧ n ⊆ U

theorem IsTopologicalBasis.isNetwork {B : Set (Set X)} (hB : IsTopologicalBasis B) :
    IsNetwork B :=
  fun _ hU _ hx => hB.exists_subset_of_mem_open hx hU

theorem isNetwork_setOf_isOpen : IsNetwork {U : Set X | IsOpen U} :=
  isTopologicalBasis_opens.isNetwork

theorem isNetwork_range_singleton [DiscreteTopology X] :
    IsNetwork (range (singleton : X → Set X)) :=
  fun _ _ x hx => ⟨{x}, mem_range_self x, rfl, singleton_subset_iff.mpr hx⟩

/-- The preimage of a network under an inducing map is a network. -/
theorem IsNetwork.preimage {N : Set (Set Y)} (hN : IsNetwork N) {f : X → Y}
    (hf : IsInducing f) : IsNetwork ((f ⁻¹' ·) '' N) := by
  intro U hU x hx
  obtain ⟨V, hV, rfl⟩ := hf.isOpen_iff.mp hU
  obtain ⟨n, hn, hfx, hnV⟩ := hN hV (f x) hx
  exact ⟨f ⁻¹' n, mem_image_of_mem _ hn, hfx, preimage_mono hnV⟩

/-- Every network for a discrete space contains all singletons. -/
theorem IsNetwork.singleton_mem [DiscreteTopology X] {N : Set (Set X)} (hN : IsNetwork N)
    (x : X) : {x} ∈ N := by
  obtain ⟨n, hn, hx, hsub⟩ := hN (isOpen_discrete {x}) x rfl
  rwa [subset_antisymm hsub (singleton_subset_iff.mpr hx)] at hn

variable (X)

/-- The *density* `d(X)` of a topological space `X` is the least cardinality of a dense subset. -/
noncomputable def density : Cardinal :=
  ⨅ s : {s : Set X // Dense s}, #s.1

/-- The *network weight* `nw(X)` of a topological space `X` is the least cardinality of a
network for `X`. -/
noncomputable def networkWeight : Cardinal :=
  ⨅ N : {N : Set (Set X) // IsNetwork N}, #N.1

variable {X}

instance : Nonempty {s : Set X // Dense s} := ⟨⟨univ, dense_univ⟩⟩

instance : Nonempty {N : Set (Set X) // IsNetwork N} := ⟨⟨_, isNetwork_setOf_isOpen⟩⟩

theorem _root_.Dense.density_le {s : Set X} (hs : Dense s) : density X ≤ #s :=
  ciInf_le' (fun s : {s : Set X // Dense s} => #s.1) ⟨s, hs⟩

theorem IsNetwork.networkWeight_le {N : Set (Set X)} (hN : IsNetwork N) :
    networkWeight X ≤ #N :=
  ciInf_le' (fun N : {N : Set (Set X) // IsNetwork N} => #N.1) ⟨N, hN⟩

theorem le_density {c : Cardinal} (h : ∀ s : Set X, Dense s → c ≤ #s) : c ≤ density X :=
  le_ciInf fun s => h s.1 s.2

theorem le_networkWeight {c : Cardinal} (h : ∀ N : Set (Set X), IsNetwork N → c ≤ #N) :
    c ≤ networkWeight X :=
  le_ciInf fun N => h N.1 N.2

/-- The density is attained by some dense subset. -/
theorem exists_dense_mk_eq_density : ∃ s : Set X, Dense s ∧ #s = density X :=
  let ⟨⟨s, hs⟩, h⟩ := ciInf_mem fun s : {s : Set X // Dense s} => #s.1
  ⟨s, hs, h⟩

/-- The network weight is attained by some network. -/
theorem exists_isNetwork_mk_eq_networkWeight :
    ∃ N : Set (Set X), IsNetwork N ∧ #N = networkWeight X :=
  let ⟨⟨N, hN⟩, h⟩ := ciInf_mem fun N : {N : Set (Set X) // IsNetwork N} => #N.1
  ⟨N, hN, h⟩

theorem density_le_aleph0_iff : density X ≤ ℵ₀ ↔ SeparableSpace X := by
  constructor
  · intro h
    obtain ⟨s, hs, hs'⟩ := exists_dense_mk_eq_density (X := X)
    exact ⟨s, countable_coe_iff.mp (mk_le_aleph0_iff.mp (hs'.trans_le h)), hs⟩
  · rintro ⟨s, hsc, hsd⟩
    exact hsd.density_le.trans (mk_le_aleph0_iff.mpr hsc.to_subtype)

theorem networkWeight_le_aleph0 [SecondCountableTopology X] : networkWeight X ≤ ℵ₀ :=
  let ⟨_, hbc, _, hb⟩ := exists_countable_basis (α := X)
  hb.isNetwork.networkWeight_le.trans (mk_le_aleph0_iff.mpr hbc.to_subtype)

/-- The network weight of a subspace is at most that of the ambient space. -/
theorem _root_.Topology.IsInducing.networkWeight_le {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsInducing f) : networkWeight X ≤ networkWeight Y :=
  let ⟨_, hN, hN'⟩ := exists_isNetwork_mk_eq_networkWeight (X := Y)
  (hN.preimage hf).networkWeight_le.trans (hN' ▸ mk_image_le)

/-- The density of a discrete space is its cardinality. -/
theorem density_eq_mk [DiscreteTopology X] : density X = #X := by
  refine le_antisymm (dense_univ.density_le.trans_eq mk_univ) (le_density fun s hs => ?_)
  obtain rfl := dense_discrete.mp hs
  exact mk_univ.ge

/-- The network weight of a discrete space is its cardinality. -/
theorem networkWeight_eq_mk [DiscreteTopology X] : networkWeight X = #X := by
  refine le_antisymm (isNetwork_range_singleton.networkWeight_le.trans mk_range_le)
    (le_networkWeight fun N hN => ?_)
  exact mk_le_of_injective (f := fun x => (⟨{x}, hN.singleton_mem x⟩ : N))
    fun _ _ h => singleton_injective (congrArg Subtype.val h)

end TopologicalSpace
