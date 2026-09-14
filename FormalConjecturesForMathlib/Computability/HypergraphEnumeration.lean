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

public import FormalConjecturesForMathlib.Computability.OutputEnumeration
public import Mathlib.Data.Finset.Powerset

/-!
# Inclusion-minimal hypergraph transversals

Hyperedges are explicit lists of binary vertex names. Repetitions are harmless.
The effective vertex set is their union: isolated vertices cannot occur in an
inclusion-minimal transversal. Empty hyperedges and the empty hypergraph are
retained and have different answers. Minimal means inclusion-minimal, not
minimum cardinality.

Reference: Mary, *Enumeration of minimal transversals of hypergraphs of bounded
VC-dimension*, §1, Trans-Enum, https://arxiv.org/html/2407.00694v3.
The finite reference enumeration is exhaustive, with no polynomial-time claim.
-/

@[expose] public section

namespace HypergraphEnumeration

abbrev Hypergraph := List (List ℕ)

def vertices (h : Hypergraph) : Finset ℕ := h.flatten.toFinset

def Transversal (h : Hypergraph) (s : Finset ℕ) : Prop :=
  ∀ e ∈ h, ∃ v ∈ e, v ∈ s

instance (h : Hypergraph) (s : Finset ℕ) : Decidable (Transversal h s) := by
  unfold Transversal
  infer_instance

def MinimalTransversal (h : Hypergraph) (s : Finset ℕ) : Prop :=
  s ⊆ vertices h ∧ Transversal h s ∧
    ∀ t ⊆ s, Transversal h t → s ⊆ t

instance (h : Hypergraph) (s : Finset ℕ) : Decidable (MinimalTransversal h s) := by
  unfold MinimalTransversal
  infer_instance

theorem Transversal.mono {h : Hypergraph} {s t : Finset ℕ}
    (hs : Transversal h s) (hst : s ⊆ t) : Transversal h t := by
  intro e he
  obtain ⟨v, hv, hvs⟩ := hs e he
  exact ⟨v, hv, hst hvs⟩

theorem transversal_cons_of_superset {h : Hypergraph} {e e' : List ℕ}
    (he : e ∈ h) (hsub : ∀ v ∈ e, v ∈ e') (s : Finset ℕ) :
    Transversal (e' :: h) s ↔ Transversal h s := by
  constructor
  · intro hs f hf
    exact hs f (List.mem_cons_of_mem _ hf)
  · intro hs f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · obtain ⟨v, hv, hvs⟩ := hs e he
      exact ⟨v, hsub v hv, hvs⟩
    · exact hs f hf

/-- The extra support restriction does not affect inclusion-minimality. -/
theorem minimalTransversal_iff (h : Hypergraph) (s : Finset ℕ) :
    MinimalTransversal h s ↔ Transversal h s ∧
      ∀ t ⊆ s, Transversal h t → s ⊆ t := by
  constructor
  · exact fun hs => hs.2
  · rintro ⟨hs, hmin⟩
    have hi : Transversal h (s ∩ vertices h) := by
      intro e he
      obtain ⟨v, hv, hvs⟩ := hs e he
      refine ⟨v, hv, Finset.mem_inter.mpr ⟨hvs, ?_⟩⟩
      simp only [vertices, List.mem_toFinset, List.mem_flatten]
      exact ⟨e, he, hv⟩
    exact ⟨fun v hv => (Finset.mem_inter.mp
      (hmin _ Finset.inter_subset_left hi hv)).2, hs, hmin⟩

/-- Duplicated or nonminimal edges do not change the mathematical answers. -/
theorem minimalTransversal_cons_of_superset {h : Hypergraph} {e e' : List ℕ}
    (he : e ∈ h) (hsub : ∀ v ∈ e, v ∈ e') (s : Finset ℕ) :
    MinimalTransversal (e' :: h) s ↔ MinimalTransversal h s := by
  simp only [minimalTransversal_iff, transversal_cons_of_superset he hsub]

def transversals (h : Hypergraph) : Finset (Finset ℕ) :=
  (vertices h).powerset.filter (MinimalTransversal h)

@[simp] theorem mem_transversals (h : Hypergraph) (s : Finset ℕ) :
    s ∈ transversals h ↔ MinimalTransversal h s := by
  simp only [transversals, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨And.right, fun hs => ⟨hs.1, hs⟩⟩

theorem minimalTransversal_empty_iff (s : Finset ℕ) :
    MinimalTransversal [] s ↔ s = ∅ := by
  constructor
  · intro hs
    simpa [vertices] using hs.1
  · rintro rfl
    simp [MinimalTransversal, vertices, Transversal]

theorem not_transversal_of_empty_edge {h : Hypergraph} (he : [] ∈ h) (s : Finset ℕ) :
    ¬ Transversal h s := by
  intro hs
  simpa using hs [] he

theorem no_transversals_of_empty_edge {h : Hypergraph} (he : [] ∈ h) :
    transversals h = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  exact not_transversal_of_empty_edge he s ((mem_transversals h s).mp hs).2.1

end HypergraphEnumeration
