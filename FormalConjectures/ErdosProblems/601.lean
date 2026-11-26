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
# Erdős Problem 601

*Reference:* [erdosproblems.com/601](https://www.erdosproblems.com/601)

*References:*
- [EHM70] Erdős, P.; Hajnal, A.; Milner, E.C. *Set mappings and polarized partition relations.*
  Combinatorial theory and its applications, I–III (Balatonfüred, 1969) (1970), 327–363.
- [Er81] Erdős, P. *On the combinatorial problems which I would most like to see solved.*
  Combinatorica 1 (1981), 25–42, Section VII.
- [La90] Larson, J.A. *Martin's Axiom and ordinal graphs: large independent sets or infinite
  paths.* Ann. Pure Appl. Logic 47 (1990), 31–39.
-/

@[expose] public section

open Cardinal Ordinal SimpleGraph

namespace Erdos601

universe u

/--
`HasPathOrIndepSetOfType α` holds for an ordinal $\alpha$ if every simple graph on
$\alpha.\mathrm{ToType}$ contains either:

1. an **infinite path** — an injective function $f : \mathbb{N} \to \alpha.\mathrm{ToType}$
   with $G.\mathrm{Adj}\, (f n)\, (f(n+1))$ for all $n$, or
2. an **independent set of order type $\alpha$** — a set $s \subseteq \alpha.\mathrm{ToType}$
   that is pairwise non-adjacent in $G$ and whose order type (under the well-order inherited
   from $\alpha$) equals $\alpha$.
-/
def HasPathOrIndepSetOfType (α : Ordinal.{u}) : Prop :=
  ∀ G : SimpleGraph α.ToType,
    (∃ f : ℕ → α.ToType, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1))) ∨
    (∃ s : Set α.ToType, G.IsIndepSet s ∧ typeLT s = α)

def erdos_601.answer : Ordinal.{0} → Prop := by sorry

/--
**Erdős Problem 601** ($500 prize).

For which limit ordinals $\alpha$ does `HasPathOrIndepSetOfType α` hold?
-/
@[category research open, question value, AMS 5]
theorem erdos_601 :
    ∀ α : Ordinal.{0}, Order.IsSuccLimit α →
      (HasPathOrIndepSetOfType α ↔
        erdos_601.answer α) := by
  sorry

/--
**Erdős–Hajnal–Milner conjecture** [Er81, Section VII]: every graph on a limit ordinal
$\alpha$ contains an infinite path or an independent set of order type $\alpha$. -/
@[category research open, AMS 5]
theorem erdos_601.variants.universal :
    ∀ α : Ordinal.{0}, Order.IsSuccLimit α → HasPathOrIndepSetOfType α := by
  sorry

namespace erdos_601.variants

/--
**Erdős–Hajnal–Milner (1970)** [EHM70]: For all limit ordinals $\alpha < \omega_1^{\omega+2}$,
every graph on $\alpha.\mathrm{ToType}$ has either an infinite path or an independent set of
order type $\alpha$.
-/
@[category research solved, AMS 5]
theorem erdos_hajnal_milner_1970 :
    ∀ α : Ordinal.{0},
      Order.IsSuccLimit α →
      α < ω_ 1 ^ (ω + 2) →
      HasPathOrIndepSetOfType α := by
  sorry

/--
**Erdős–Hajnal–Milner conjecture at $\omega_1^{\omega+2}$** [Er81, Section VII]: every
graph on $\omega_1^{\omega+2}$ contains an infinite path or an independent set of that
order type. Erdős conjectured the positive answer. This is the first limit ordinal not
covered by the Erdős–Hajnal–Milner theorem.
-/
@[category research open, AMS 5]
theorem omega_1_omega_plus_2 :
    HasPathOrIndepSetOfType (ω_ 1 ^ (ω + 2)) := by
  sorry

/-
**Larson (1990)** [La90] showed that under Martin's Axiom (MA), the property
`HasPathOrIndepSetOfType α` holds for all limit ordinals $\alpha < 2^{\aleph_0}$. We do
not state this here as a Lean theorem because Martin's Axiom is not yet formalised in
Mathlib (and a bare `MA : Prop` placeholder would not faithfully encode the axiom).
-/

/-- `HasPathOrIndepSetOfType ω` in a fixed universe: Ramsey for pairs along an injective
sequence gives a path or an infinite independent set, and an infinite subset of `ω` has order
type `ω`. -/
@[category API, AMS 5]
private theorem at_omega_aux : HasPathOrIndepSetOfType.{u} ω := by
  intro G
  have : Infinite (ω : Ordinal.{u}).ToType :=
    Cardinal.infinite_iff.2 (le_of_eq (by rw [Cardinal.mk_toType, Ordinal.card_omega0]))
  let e := Infinite.natEmbedding (ω : Ordinal.{u}).ToType
  obtain ⟨g, hpath | hind⟩ := exists_increasing_or_nonincreasing_subseq' G.Adj e
  · exact Or.inl ⟨fun n => e (g n), e.injective.comp g.injective, hpath⟩
  have hinj : Function.Injective fun n => e (g n) := e.injective.comp g.injective
  refine Or.inr ⟨Set.range fun n => e (g n), (isIndepSet_iff G).2 ?_, le_antisymm ?_ ?_⟩
  · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ hmn
    rcases lt_trichotomy m n with h | rfl | h
    · exact hind m n h
    · exact absurd rfl hmn
    · exact fun hadj => hind n m h hadj.symm
  · exact (Ordinal.type_set_le _).trans (Ordinal.type_toType ω).le
  · by_contra h
    have hcard := Ordinal.card_lt_aleph0.2 (not_le.1 h)
    rw [Ordinal.card_type] at hcard
    exact Set.infinite_range_of_injective hinj
      (Set.finite_coe_iff.1 (Cardinal.lt_aleph0_iff_finite.1 hcard))

/--
**Base case $\alpha = \omega$**: `HasPathOrIndepSetOfType ω` holds.

Every countably infinite graph on vertex set $\omega$ either contains an infinite path or
has an infinite independent set (and an infinite set has order type $\omega$). Follows from
Ramsey-theoretic arguments (or directly from the Erdős–Hajnal–Milner result since
$\omega < \omega_1^{\omega+2}$).
-/
@[category research solved, AMS 5]
theorem at_omega : HasPathOrIndepSetOfType ω :=
  at_omega_aux

end erdos_601.variants

end Erdos601
