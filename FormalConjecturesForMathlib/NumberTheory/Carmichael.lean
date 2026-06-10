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

public import Mathlib
public import FormalConjecturesForMathlib.Data.Nat.Prime.Composite

open scoped Nat

@[expose] public section

/-!
# Carmichael Numbers

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Carmichael_number)
-/

/--
A Carmichael number is a composite number `n` such that for all `b ≥ 1`,
we have `b^n ≡ b (mod n)`.
-/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ b ≥ 1, n.Coprime b → n.FermatPsp b

/-- A composite Carmichael number is squarefree. -/
theorem squarefree_of_isCarmichael {a : ℕ} (ha₁ : a.Composite) (ha₂ : IsCarmichael a) :
    Squarefree a := by
  have ha₂_forall := ha₂.2.2
  simp_all [Nat.Composite, a.squarefree_iff_prime_squarefree, Nat.FermatPsp, Nat.ProbablePrime]
  rintro p hp ⟨N, rfl⟩
  apply absurd (ha₂_forall (p * N + 1) ((1).le_add_left _))
  have : Fact p.Prime := ⟨hp⟩
  rw [mul_assoc] at ha₁
  rw [mul_assoc, ← geom_sum_mul_of_one_le ((1).le_add_left (p * N)), p.coprime_mul_iff_left]
  simpa using (mul_dvd_mul_iff_right fun _ ↦ by simp_all only [mul_zero, not_lt_zero']).not.mpr
    ((ZMod.natCast_eq_zero_iff _ _).not.mp (by simp [le_of_lt ha₁.1]))

/-- A composite number `a` is Carmichael if and only if it is squarefree
and, for all prime `p` dividing `a`, we have `p - 1 ∣ a - 1`. -/
theorem korselts_criterion (a : ℕ) (ha₁ : a.Composite) :
    IsCarmichael a ↔ Squarefree a ∧
      ∀ p, p.Prime → p ∣ a → (p - 1 : ℕ) ∣ (a - 1 : ℕ) := by
  refine ⟨fun h ↦ ⟨squarefree_of_isCarmichael ha₁ h, fun p hp hpa ↦ ?_⟩, fun h ↦ ⟨ha₁.1, ha₁.2, fun b hb hab ↦ ?_⟩⟩
  · have h_forall := h.2.2
    have : Fact p.Prime := ⟨hp⟩
    let ⟨g, h⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    obtain ⟨k, rfl⟩ := hpa
    have hk : k.Coprime p := by
      by_contra hk
      obtain ⟨_, rfl⟩ := not_not.1 <| hp.coprime_iff_not_dvd.not.1 <| mt Nat.Coprime.symm hk
      absurd (squarefree_of_isCarmichael ha₁ h)
      simp [← mul_assoc, mul_comm, Nat.squarefree_mul_iff, ← sq, Nat.squarefree_pow_iff hp.ne_one]
    simp_all [IsCarmichael, Nat.FermatPsp, Nat.ProbablePrime, Nat.Composite]
    let e : ZMod (p * k) ≃+* ZMod p × ZMod k := ZMod.chineseRemainder hk.symm
    let s : ZMod (p * k) := e.symm (g, 1)
    have : NeZero k := ⟨fun _ => by simp_all⟩
    have : p * k ∣ (e.symm (g, 1)).val ^ (p * k - 1) - 1 := h_forall _ (ZMod.val_pos.2 (by aesop))
      ((ZMod.isUnit_iff_coprime _ _).1 (by simp [Prod.isUnit_iff])).symm
    simp_all [p.totient_prime, sub_eq_zero, ZMod.val_pos, ← ZMod.natCast_eq_zero_iff,
      ← map_pow, ← Units.val_pow_eq_pow_val, ← orderOf_dvd_iff_pow_eq_one,
      orderOf_eq_card_of_forall_mem_zpowers]
  · obtain ⟨h_sqfr, h_dvd⟩ := h
    simp_all [a.squarefree_iff_prime_squarefree, Nat.FermatPsp, Nat.ProbablePrime, Nat.Composite]
    refine if hb : b ^ (a - 1) - 1 = 0 then ⟨0, hb⟩ else (a.factorization_le_iff_dvd ha₁.1.ne_bot hb).1 fun p => ?_
    by_cases hp : p.Prime
    · by_cases hpa : p ∣ a
      · obtain ⟨w, h⟩ := h_dvd p hp hpa
        obtain ⟨ha₁, ha₂⟩ := ha₁
        apply Nat.Prime.pow_dvd_iff_le_factorization hp hb |>.1
        have : a.factorization p ≤ 1 := not_lt.1 fun h =>
          h_sqfr p hp <| (sq p ▸ (pow_dvd_pow p h).trans (a.ordProj_dvd p))
        replace : a.factorization p = 1 :=
          this.antisymm (hp.dvd_iff_one_le_factorization (by grind) |>.1 hpa)
        simp_rw [this, pow_one, ← CharP.cast_eq_zero_iff (ZMod p)]
        have one_le_b_pow : 1 ≤ b ^ (a - 1) := by omega
        push_cast [one_le_b_pow]
        simp_rw [h, pow_mul]
        simp_all +decide [CharP.cast_eq_zero_iff _ p,
          hp.coprime_iff_not_dvd.1 (hab.of_dvd_left (by aesop)), ZMod.pow_card_sub_one_eq_one]
      · simp [a.factorization_eq_zero_of_not_dvd hpa]
    · simp_all
