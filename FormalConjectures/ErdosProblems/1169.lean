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
# Erdős Problem 1169

*Reference:* [erdosproblems.com/1169](https://www.erdosproblems.com/1169)

*References:*
- [Ha71] Hajnal, A. *A negative partition relation.* Proc. Nat. Acad. Sci. U.S.A. 68 (1971),
  pp. 142–144.
- [Va99] Vaughan, J.E. *Open problems in topology II*, problem 7.85 (1999).
-/

open Cardinal Ordinal
open scoped Cardinal

namespace Erdos1169

universe u

/-- Local copy of the binary ordinal Ramsey predicate $\alpha \to (\beta, \gamma)^2$:
every 2-coloring of pairs from $\alpha$ admits a red clique of order type $\beta$ or a
blue clique of order type $\gamma$.

Will be replaced by `OrdinalRamsey` from `FormalConjecturesForMathlib/SetTheory/Ordinal/
PartitionRelation.lean` once that lands (see PR #4195). -/
def OrdinalRamsey (α β γ : Ordinal.{u}) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
    (∃ s, blue.IsClique s ∧ typeLT s = γ)

/- ### The main open problem -/

/--
**Erdős Problem 1169** (problem of Erdős and Hajnal). For every finite $k$, does the
negative ordinal Ramsey relation $\omega_1^2 \not\to (\omega_1^2, k)^2$ hold?

That is: is there a 2-coloring of pairs from $\omega_1^2$ such that no subset of order
type $\omega_1^2$ is red-monochromatic, and no $k$-element subset is blue-monochromatic?

**Status.** NOT DISPROVABLE — open in general, but Hajnal [Ha71] proved it under the
Continuum Hypothesis. See also [erdosproblems.com/592](https://www.erdosproblems.com/592)
for the analogous question over countable ordinals.
-/
@[category research open, AMS 3]
theorem erdos_1169 :
    answer(sorry) ↔
    ∀ k : ℕ, ¬ OrdinalRamsey ((ω_ 1) ^ (2 : ℕ)) ((ω_ 1) ^ (2 : ℕ)) (k : Ordinal) := by
  sorry

/- ### Variants and known results -/

namespace erdos_1169.variants

/--
**Single-$k$ form**. The Erdős–Hajnal question specialised to $k = 3$ (the literal form
on erdosproblems.com): does $\omega_1^2 \not\to (\omega_1^2, 3)^2$ hold?
-/
@[category research open, AMS 3]
theorem at_three : answer(sorry) ↔
    ¬ OrdinalRamsey ((ω_ 1) ^ (2 : ℕ)) ((ω_ 1) ^ (2 : ℕ)) (3 : Ordinal) := by
  sorry

/--
**Hajnal (1971), assuming CH.** Under the Continuum Hypothesis,
$\omega_1^2 \not\to (\omega_1^2, k)^2$ holds for every finite $k$.
-/
@[category research solved, AMS 3]
theorem hajnal_under_ch (hCH : 𝔠 = ℵ_ 1) :
    ∀ k : ℕ, ¬ OrdinalRamsey ((ω_ 1) ^ (2 : ℕ)) ((ω_ 1) ^ (2 : ℕ)) (k : Ordinal) := by
  sorry

end erdos_1169.variants

/- ### Sanity checks -/

/-- **Monotonicity in the blue side.** If the ordinal Ramsey relation holds with blue
target $\gamma$, it holds with any smaller blue target $\gamma' \le \gamma$. -/
@[category test, AMS 3]
theorem ordinalRamsey_mono_blue {α β γ γ' : Ordinal.{u}}
    (h : OrdinalRamsey α β γ) (hγ : γ' ≤ γ) :
    OrdinalRamsey α β γ' := by
  intro red blue hCompl
  obtain (⟨s, hred, htype⟩ | ⟨s, hblue, htype⟩) := h red blue hCompl
  · exact Or.inl ⟨s, hred, htype⟩
  · -- s has type γ; find a sub-clique of type γ' ≤ γ.
    rw [← Ordinal.type_toType γ'] at hγ
    obtain ⟨g⟩ := Ordinal.type_le_iff'.mp (htype ▸ hγ)
    let t : Set α.ToType := Set.range (Subtype.val ∘ g)
    refine Or.inr ⟨t, ?_, ?_⟩
    · -- t is a blue clique
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
      apply hblue (g a).2 (g b).2
      intro h
      apply hne
      simp [h]
    · -- typeLT t = γ'
      let emb : (· < · : γ'.ToType → γ'.ToType → Prop) ↪r (· < · : ↑t → ↑t → Prop) :=
        { toFun := fun a => ⟨(g a).val, a, rfl⟩
          inj' := fun a b heq =>
            g.injective (Subtype.ext (congr_arg (fun x : ↑t => x.val) heq))
          map_rel_iff' := g.map_rel_iff }
      have hsurj : Function.Surjective emb :=
        fun ⟨_, hy⟩ => ⟨hy.choose, Subtype.ext hy.choose_spec⟩
      exact (Ordinal.type_eq.mpr ⟨RelIso.ofSurjective emb hsurj |>.symm⟩).trans
        (Ordinal.type_toType γ')

end Erdos1169
