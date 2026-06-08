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
import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1173

*Reference:* [erdosproblems.com/1173](https://www.erdosproblems.com/1173)
-/

open Cardinal Ordinal

open scoped Cardinal Ordinal

namespace Erdos1173

/-- The **set mapping condition** for `f : ω_{ω+1} → 𝒫(ω_{ω+1})`:
self-avoidance (`α ∉ f α`), image bound (`#(f α) ≤ ℵ_ω`), and almost-disjoint
images (`#(f α ∩ f β) < ℵ_ω` for `α ≠ β`). -/
def IsSetMapping (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) : Prop :=
  (∀ α : (ω_ (ω + 1)).ToType, α ∉ f α) ∧
  (∀ α : (ω_ (ω + 1)).ToType, #(f α) ≤ ℵ_ ω) ∧
  (∀ α β : (ω_ (ω + 1)).ToType, α ≠ β → #(f α ∩ f β : Set (ω_ (ω + 1)).ToType) < ℵ_ ω)

/-- A set `Y ⊆ ω_{ω+1}` is **free** for `f` if for all distinct `α, β ∈ Y`,
`β ∉ f α`. -/
def IsFreeSet (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType)
    (Y : Set (ω_ (ω + 1)).ToType) : Prop :=
  ∀ α ∈ Y, ∀ β ∈ Y, α ≠ β → β ∉ f α

/--
**Erdős–Hajnal Problem 1173** [EH74]. Assume GCH. Let
$f : \omega_{\omega+1} \to [\omega_{\omega+1}]^{\leq \aleph_\omega}$
be a set mapping such that $|f(\alpha) \cap f(\beta)| < \aleph_\omega$ for all
$\alpha \neq \beta$. Does there exist a free set of cardinality $\aleph_{\omega+1}$?
-/
@[category research open, AMS 3]
theorem erdos_1173 : answer(sorry) ↔
    GCH →
    ∀ f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType,
      IsSetMapping f →
      ∃ Y : Set (ω_ (ω + 1)).ToType, IsFreeSet f Y ∧ #Y = ℵ_ (ω + 1) := by
  sorry

/-- The initial ordinal `ω_{ω+1}` has cardinality `ℵ_{ω+1}`. -/
@[category test, AMS 3]
theorem erdos_1173.sanity.card_domain :
    #(ω_ (ω + 1)).ToType = ℵ_ (ω + 1) := by
  rw [mk_toType, Ordinal.card_omega]

/-- `ℵ_ω < ℵ_{ω+1}`: free-set size is strictly above the image-bound, making
the problem non-trivial. -/
@[category test, AMS 3]
theorem erdos_1173.sanity.aleph_omega_lt_succ : ℵ_ ω < ℵ_ (ω + 1) := by
  exact Cardinal.aleph_lt_aleph.mpr (Order.lt_succ ω)

/-- The empty set is always free for any `f`. -/
@[category test, AMS 3]
theorem erdos_1173.sanity.empty_is_free
    (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) :
    IsFreeSet f ∅ := by
  intro _ hα
  simp at hα

/-- A singleton `{α}` is always free for any `f` (the `α ≠ β` premise is vacuous). -/
@[category test, AMS 3]
theorem erdos_1173.sanity.singleton_is_free
    (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType)
    (α : (ω_ (ω + 1)).ToType) :
    IsFreeSet f {α} := by
  intro a ha b hb hab
  simp only [Set.mem_singleton_iff] at ha hb
  exact absurd (ha ▸ hb ▸ rfl) hab

/-- Free sets are downward-closed under inclusion. -/
@[category textbook, AMS 3]
theorem erdos_1173.variants.free_set_mono
    (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType)
    {Y Z : Set (ω_ (ω + 1)).ToType}
    (hYZ : Z ⊆ Y) (hY : IsFreeSet f Y) : IsFreeSet f Z := by
  intro α hα β hβ hne
  exact hY α (hYZ hα) β (hYZ hβ) hne

/-- Under `IsSetMapping f`, each image has cardinality `< ℵ_{ω+1}`. -/
@[category textbook, AMS 3]
theorem erdos_1173.variants.image_lt_aleph_succ
    (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType)
    (hf : IsSetMapping f)
    (α : (ω_ (ω + 1)).ToType) :
    #(f α) < ℵ_ (ω + 1) := by
  exact (hf.2.1 α).trans_lt (Cardinal.aleph_lt_aleph.mpr (Order.lt_succ ω))

end Erdos1173
