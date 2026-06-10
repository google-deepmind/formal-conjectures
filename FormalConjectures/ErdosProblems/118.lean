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
# Erdős Problem 118

*Reference:* [erdosproblems.com/118](https://www.erdosproblems.com/118)

*References:*
- [Sc99] Schipperus, R. *Countable partition ordinals.* Thesis, University of Colorado (1999).
- [Sc10] Schipperus, R. *Countable partition ordinals.* Ann. Pure Appl. Logic 161 (2010),
  1195–1215.
- [Da99] Darby, C. *Negative partition relations for ordinals $\omega^{\omega^\delta}$.*
  J. Combin. Theory Ser. B 76 (1999), 205–222.
- [La00] Larson, J. A. *An ordinal partition avoiding pentagrams.* J. Symbolic Logic 65
  (2000), 969–978.
- [HST10] Hajnal, A.; Larson, J. A. *Partition relations.* Handbook of set theory,
  Springer (2010), 129–213.
-/

open Cardinal Ordinal
open scoped Cardinal

namespace Erdos118

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

/- ### The main problem -/

/--
**Erdős Problem 118** (problem of Erdős and Hajnal). Let $\alpha$ be such that
$\alpha \to (\alpha, 3)^2$. For every $n \ge 3$, must $\alpha \to (\alpha, n)^2$?

The original question is asked for cardinals, ordinals, and order types; we state the
ordinal version, which is the standard reading: ordinals $\alpha$ with
$\alpha \to (\alpha, 3)^2$ are called *partition ordinals*.

The answer is **no**, shown independently by Schipperus [Sc99, Sc10] and Darby [Da99].
Larson [La00] gave the concrete counterexample $\alpha = \omega^{\omega^2}$, for which
$\alpha \to (\alpha, 3)^2$ holds yet $\alpha \not\to (\alpha, 5)^2$. See Chapter 2.9 of
[HST10] for further background.
-/
@[category research solved, AMS 3]
theorem erdos_118 :
    answer(False) ↔ ∀ α : Ordinal.{0}, OrdinalRamsey α α 3 →
      ∀ n : ℕ, 3 ≤ n → OrdinalRamsey α α n := by
  sorry

/- ### Known results -/

namespace erdos_118.variants

/--
**Larson (2000).** The ordinal $\alpha = \omega^{\omega^2}$ is a partition ordinal,
$\omega^{\omega^2} \to (\omega^{\omega^2}, 3)^2$, yet
$\omega^{\omega^2} \not\to (\omega^{\omega^2}, 5)^2$ [La00], so the answer to the
Erdős–Hajnal question is negative already at $n = 5$.
-/
@[category research solved, AMS 3]
theorem larson : OrdinalRamsey (ω ^ ω ^ (2 : Ordinal)) (ω ^ ω ^ (2 : Ordinal)) 3 ∧
    ¬ OrdinalRamsey (ω ^ ω ^ (2 : Ordinal)) (ω ^ ω ^ (2 : Ordinal)) 5 := by
  sorry

end erdos_118.variants

/- ### Sanity checks -/

/-- **Monotonicity in the blue side.** If the ordinal Ramsey relation holds with blue
target $\gamma$, it holds with any smaller blue target $\gamma' \le \gamma$. In
particular a failure of $\alpha \to (\alpha, n)^2$ for some $n \ge 3$ is genuinely
stronger than a failure of $\alpha \to (\alpha, 3)^2$. -/
@[category test, AMS 3]
theorem ordinalRamsey_mono_blue {α β γ γ' : Ordinal.{u}}
    (hγ : γ' ≤ γ) (h : OrdinalRamsey α β γ) :
    OrdinalRamsey α β γ' := by
  intro red blue hCompl
  obtain (⟨s, hred, htype⟩ | ⟨s, hblue, htype⟩) := h red blue hCompl
  · exact Or.inl ⟨s, hred, htype⟩
  · -- s has type γ; find a sub-clique of type γ'.
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

end Erdos118
