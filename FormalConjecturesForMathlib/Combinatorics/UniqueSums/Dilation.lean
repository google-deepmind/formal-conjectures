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

public import FormalConjecturesForMathlib.Combinatorics.UniqueSums.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# Dilations and representation counts

This file proves the finite-field dilation lemma of Łuczak–Schoen and transports uniform lower
bounds on representation counts through injective dilations.

Reference:
- [LS08] Łuczak, Tomasz and Schoen, Tomasz. "On the number of unique sums."
-/

open Finset
open scoped Pointwise

namespace UniqueSums

open Finset

variable {p : ℕ} [Fact p.Prime]

/--
[LS08, Lemma 4]: if `(|A| * |B|)² < p` then some nonzero dilate separates all sums,
`|A + x₀ • B| = |A| * |B|`. (The paper states the hypothesis as `|A||B| < √p`;
we square it to stay in `ℕ`.) Pigeonhole over the field `ZMod p`: a coincidence
`a + x•b = a' + x•b'` determines `x` uniquely, and there are fewer than `p - 1`
possible coincidences.
-/
theorem exists_dilate_card_add_eq {A B : Finset (ZMod p)}
    (hAB : (A.card * B.card) ^ 2 < p) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ x₀ : ZMod p, x₀ ≠ 0 ∧ (A + B.image (x₀ * ·)).card = A.card * B.card := by
  classical
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let D := A ×ˢ B
  let X := (Finset.univ : Finset (ZMod p)).erase 0
  have isUnit_of_ne_zero (x : ZMod p) (hx : x ≠ 0) : IsUnit x := by
    rw [← ZMod.natCast_zmod_val x]
    apply (ZMod.isUnit_iff_coprime x.val p).mpr
    apply Nat.Coprime.symm
    apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
    intro hdiv
    apply hx
    rw [← ZMod.natCast_zmod_val x, ZMod.natCast_eq_zero_iff]
    exact hdiv
  have hcard_of_inj (x : ZMod p) (hx : x ≠ 0)
      (hinj : Set.InjOn (fun q : ZMod p × ZMod p ↦ q.1 + x * q.2) ↑D) :
      (A + B.image (x * ·)).card = A.card * B.card := by
    have hmul : Function.Injective (x * ·) := (isUnit_of_ne_zero x hx).mul_right_injective
    calc
      (A + B.image (x * ·)).card = A.card * (B.image (x * ·)).card := by
        apply Finset.card_add_iff.mpr
        intro q hq q' hq' heq
        simp only [Set.mem_prod, Finset.mem_coe] at hq hq'
        rcases Finset.mem_image.mp hq.2 with ⟨b, hb, hbc⟩
        rcases Finset.mem_image.mp hq'.2 with ⟨b', hb', hbc'⟩
        have hp : (q.1, b) = (q'.1, b') := hinj
          (show (q.1, b) ∈ D from by simp only [D, Finset.mem_product, hq.1, hb, and_self])
          (show (q'.1, b') ∈ D from by simp only [D, Finset.mem_product, hq'.1, hb', and_self])
          (by simpa only [hbc, hbc'] using heq)
        rcases Prod.mk_inj.mp hp with ⟨haeq, hbeq⟩
        apply Prod.ext
        · exact haeq
        · exact hbc.symm.trans ((congrArg (x * ·) hbeq).trans hbc')
      _ = A.card * B.card := by rw [Finset.card_image_of_injective B hmul]
  by_contra hnone
  push_neg at hnone
  have hbad (x : ↑X) :
      ¬ Set.InjOn (fun q : ZMod p × ZMod p ↦ q.1 + x.1 * q.2) ↑D := by
    intro hinj
    exact hnone x.1 (Finset.mem_erase.mp x.2).1 (hcard_of_inj x.1
      (Finset.mem_erase.mp x.2).1 hinj)
  have hcollision (x : ↑X) : ∃ qr : ↑D.offDiag,
      qr.1.1.1 + x.1 * qr.1.1.2 = qr.1.2.1 + x.1 * qr.1.2.2 := by
    have hx := hbad x
    rw [Set.InjOn] at hx
    push_neg at hx
    rcases hx with ⟨q, hq, r, hr, heq, hne⟩
    exact ⟨⟨(q, r), Finset.mem_offDiag.mpr ⟨hq, hr, hne⟩⟩, heq⟩
  choose c hc using hcollision
  have hc_inj : Function.Injective c := by
    intro x y hxy
    have hcy := hc y
    rw [← hxy] at hcy
    have hbne : (c x).1.1.2 ≠ (c x).1.2.2 := by
      intro hb
      have ha : (c x).1.1.1 = (c x).1.2.1 := by
        apply add_right_cancel
        simpa only [hb] using hc x
      exact (Finset.mem_offDiag.mp (c x).2).2.2 (Prod.ext ha hb)
    apply Subtype.ext
    apply (isUnit_of_ne_zero _ (sub_ne_zero.mpr hbne)).mul_right_cancel
    have hxrel : x.1 * ((c x).1.1.2 - (c x).1.2.2) =
        (c x).1.2.1 - (c x).1.1.1 := by
      rw [mul_sub, sub_eq_sub_iff_add_eq_add]
      simpa only [add_comm] using hc x
    have hyrel : y.1 * ((c x).1.1.2 - (c x).1.2.2) =
        (c x).1.2.1 - (c x).1.1.1 := by
      rw [mul_sub, sub_eq_sub_iff_add_eq_add]
      simpa only [add_comm] using hcy
    exact hxrel.trans hyrel.symm
  have hcount : X.card ≤ D.offDiag.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective c hc_inj
  have hDpos : 0 < D.card := Finset.card_pos.mpr (hA.product hB)
  have hsquare : D.card * D.card < p := by
    simpa only [D, Finset.card_product, pow_two] using hAB
  have hoffdiag : D.offDiag.card < D.card * D.card := by
    rw [Finset.offDiag_card]
    exact Nat.sub_lt (Nat.mul_pos hDpos hDpos) hDpos
  have hXcard : X.card = p - 1 := by
    dsimp only [X]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card p]
  rw [hXcard] at hcount
  omega

omit [Fact (Nat.Prime p)] in
/-- `MinRep` is preserved by dilation: multiplying a set by a unit permutes the
representation pairs of each sum, so the minimum representation count is unchanged. -/
theorem minRep_image_mul {S : Finset (ZMod p)} {x : ZMod p} {k : ℕ}
    (hmul : Function.Injective (x * ·)) (hS : MinRep S k) :
    MinRep (S.image (x * ·)) k := by
  intro g hg
  rcases Finset.mem_add.mp hg with ⟨u, hu, v, hv, huv⟩
  rcases Finset.mem_image.mp hu with ⟨a, ha, hau⟩
  rcases Finset.mem_image.mp hv with ⟨b, hb, hbv⟩
  let R := ((S ×ˢ S).filter fun q ↦ q.1 + q.2 = a + b)
  let T := (((S.image (x * ·)) ×ˢ (S.image (x * ·))).filter
    fun q ↦ q.1 + q.2 = g)
  have hmap : Set.MapsTo (fun q : ZMod p × ZMod p ↦ (x * q.1, x * q.2)) ↑R T := by
    intro q hq
    simp only [R, T, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq ⊢
    refine ⟨⟨Finset.mem_image.mpr ⟨q.1, hq.1.1, rfl⟩,
      Finset.mem_image.mpr ⟨q.2, hq.1.2, rfl⟩⟩, ?_⟩
    calc
      x * q.1 + x * q.2 = x * (q.1 + q.2) := (mul_add x q.1 q.2).symm
      _ = x * (a + b) := congrArg (x * ·) hq.2
      _ = x * a + x * b := mul_add x a b
      _ = u + v := by rw [hau, hbv]
      _ = g := huv
  have hinj : Set.InjOn (fun q : ZMod p × ZMod p ↦ (x * q.1, x * q.2)) ↑R := by
    intro q _ q' _ heq
    apply Prod.ext
    · exact hmul (congrArg Prod.fst heq)
    · exact hmul (congrArg Prod.snd heq)
  have hcard : R.card ≤ T.card := Finset.card_le_card_of_injOn _ hmap hinj
  change k ≤ T.card
  exact (hS (a + b) (Finset.add_mem_add ha hb)).trans hcard

end UniqueSums
