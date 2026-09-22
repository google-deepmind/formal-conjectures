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
the *density* `d(X)` and the *network weight* `nw(X)`. As usual, both are made infinite by adding
`ℵ₀`, following the convention for cardinal invariants in Felix Pernegger's
[pibase-lean](https://github.com/felixpernegger/pibase-lean)
(`PiBaseLean/AdditionalDefs/Cardinal.lean`).
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

/-- The preimage of a network under an inducing map is a network. -/
theorem IsNetwork.preimage {N : Set (Set Y)} (hN : IsNetwork N) {f : X → Y}
    (hf : IsInducing f) : IsNetwork ((f ⁻¹' ·) '' N) := by
  intro U hU x hx
  obtain ⟨V, hV, rfl⟩ := hf.isOpen_iff.mp hU
  obtain ⟨n, hn, hfx, hnV⟩ := hN hV (f x) hx
  exact ⟨f ⁻¹' n, mem_image_of_mem _ hn, hfx, preimage_mono hnV⟩

variable (X)

/-- The *density* `d(X)` of a topological space `X`: the least cardinality of a dense subset,
plus `ℵ₀`. -/
noncomputable def density : Cardinal :=
  (⨅ s : {s : Set X // Dense s}, #s.1) + ℵ₀

/-- The *network weight* `nw(X)` of a topological space `X`: the least cardinality of a network,
plus `ℵ₀`. -/
noncomputable def networkWeight : Cardinal :=
  (⨅ N : {N : Set (Set X) // IsNetwork N}, #N.1) + ℵ₀

variable {X}

instance : Nonempty {s : Set X // Dense s} := ⟨⟨univ, dense_univ⟩⟩

instance : Nonempty {N : Set (Set X) // IsNetwork N} := ⟨⟨_, isNetwork_setOf_isOpen⟩⟩

theorem aleph0_le_density : ℵ₀ ≤ density X := le_add_self

theorem aleph0_le_networkWeight : ℵ₀ ≤ networkWeight X := le_add_self

theorem _root_.Dense.density_le {s : Set X} (hs : Dense s) : density X ≤ #s + ℵ₀ :=
  add_le_add_left (ciInf_le' (fun s : {s : Set X // Dense s} => #s.1) ⟨s, hs⟩) _

theorem IsNetwork.networkWeight_le {N : Set (Set X)} (hN : IsNetwork N) :
    networkWeight X ≤ #N + ℵ₀ :=
  add_le_add_left (ciInf_le' (fun N : {N : Set (Set X) // IsNetwork N} => #N.1) ⟨N, hN⟩) _

theorem density_le_mk_add_aleph0 : density X ≤ #X + ℵ₀ :=
  dense_univ.density_le.trans_eq (by rw [mk_univ])

/-- The sets `⋂₀ {U | IsOpen U ∧ x ∈ U}`, for `x : X`, form a network of `X`. -/
theorem isNetwork_range_sInter : IsNetwork (range fun x : X => ⋂₀ {U | IsOpen U ∧ x ∈ U}) :=
  fun _ hU x hx => ⟨_, mem_range_self x, fun _ hV => hV.2, fun _ hy => hy _ ⟨hU, hx⟩⟩

theorem networkWeight_le_mk_add_aleph0 : networkWeight X ≤ #X + ℵ₀ :=
  isNetwork_range_sInter.networkWeight_le.trans (add_le_add_left mk_range_le _)

/-- The density is attained by some dense subset. -/
theorem exists_dense_mk_add_aleph0_eq_density : ∃ s : Set X, Dense s ∧ #s + ℵ₀ = density X :=
  let ⟨⟨s, hs⟩, h⟩ := ciInf_mem fun s : {s : Set X // Dense s} => #s.1
  ⟨s, hs, congrArg (· + ℵ₀) h⟩

/-- The network weight is attained by some network. -/
theorem exists_isNetwork_mk_add_aleph0_eq_networkWeight :
    ∃ N : Set (Set X), IsNetwork N ∧ #N + ℵ₀ = networkWeight X :=
  let ⟨⟨N, hN⟩, h⟩ := ciInf_mem fun N : {N : Set (Set X) // IsNetwork N} => #N.1
  ⟨N, hN, congrArg (· + ℵ₀) h⟩

theorem le_density {c : Cardinal} (h : ∀ s : Set X, Dense s → c ≤ #s + ℵ₀) : c ≤ density X :=
  let ⟨s, hs, h'⟩ := exists_dense_mk_add_aleph0_eq_density (X := X)
  h' ▸ h s hs

theorem le_networkWeight {c : Cardinal} (h : ∀ N : Set (Set X), IsNetwork N → c ≤ #N + ℵ₀) :
    c ≤ networkWeight X :=
  let ⟨N, hN, h'⟩ := exists_isNetwork_mk_add_aleph0_eq_networkWeight (X := X)
  h' ▸ h N hN

theorem density_le_aleph0_iff : density X ≤ ℵ₀ ↔ SeparableSpace X := by
  constructor
  · intro h
    obtain ⟨s, hs, hs'⟩ := exists_dense_mk_add_aleph0_eq_density (X := X)
    exact ⟨s, countable_coe_iff.mp (mk_le_aleph0_iff.mp (le_self_add.trans (hs'.trans_le h))),
      hs⟩
  · rintro ⟨s, hsc, hsd⟩
    exact hsd.density_le.trans ((add_le_add_left (mk_le_aleph0_iff.mpr hsc.to_subtype) _).trans_eq
      aleph0_add_aleph0)

theorem networkWeight_le_aleph0 [SecondCountableTopology X] : networkWeight X ≤ ℵ₀ :=
  let ⟨_, hbc, _, hb⟩ := exists_countable_basis (α := X)
  hb.isNetwork.networkWeight_le.trans
    ((add_le_add_left (mk_le_aleph0_iff.mpr hbc.to_subtype) _).trans_eq aleph0_add_aleph0)

/-- The network weight of a subspace is at most that of the ambient space. -/
theorem _root_.Topology.IsInducing.networkWeight_le {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsInducing f) :
    networkWeight X ≤ networkWeight Y :=
  let ⟨_, hN, hN'⟩ := exists_isNetwork_mk_add_aleph0_eq_networkWeight (X := Y)
  (hN.preimage hf).networkWeight_le.trans (hN' ▸ add_le_add_left mk_image_le _)

theorem density_discrete [DiscreteTopology X] : density X = #X + ℵ₀ := by
  refine le_antisymm density_le_mk_add_aleph0 (le_density fun s hs => ?_)
  obtain rfl := dense_discrete.mp hs
  rw [mk_univ]

theorem networkWeight_discrete [DiscreteTopology X] : networkWeight X = #X + ℵ₀ := by
  refine le_antisymm networkWeight_le_mk_add_aleph0 (le_networkWeight fun N hN => ?_)
  have h (x : X) : {x} ∈ N := by
    obtain ⟨n, hn, hx, hsub⟩ := hN (isOpen_discrete {x}) x rfl
    rwa [subset_antisymm hsub (singleton_subset_iff.mpr hx)] at hn
  exact add_le_add_left (mk_le_of_injective (f := fun x => (⟨{x}, h x⟩ : N))
    fun _ _ h => singleton_injective (congrArg Subtype.val h)) _

end TopologicalSpace
