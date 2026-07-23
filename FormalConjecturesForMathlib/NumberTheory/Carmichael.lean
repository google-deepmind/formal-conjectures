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

public import FormalConjecturesForMathlib.Data.Nat.Prime.Composite
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.FermatPsp

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
  Nat.Composite n ∧ ∀ b : ℕ, n ∣ b ^ n - b

/--
An equivalent formulation of Carmichael numbers, requiring the Fermat pseudoprime
property for all coprime bases.
-/
def IsCarmichael' (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ b ≥ 1, n.Coprime b → n.FermatPsp b

lemma isCarmichael'_of_isCarmichael {n : ℕ} (h : IsCarmichael n) : IsCarmichael' n := by
  have h_comp := h.1
  refine ⟨h_comp.1, h_comp.2, fun b _ hnb => ?_⟩
  have h_dvd := h.2 b
  have h_sub : b ^ n - b = b * (b ^ (n - 1) - 1) := by
    have hn : 1 ≤ n := by omega
    have h_pow : b ^ n = b * b ^ (n - 1) := by
      calc b ^ n = b ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn]
      _ = b ^ (n - 1) * b ^ 1 := by rw [pow_add]
      _ = b * b ^ (n - 1) := by rw [pow_one, mul_comm]
    rw [h_pow, Nat.mul_sub_left_distrib, mul_one]
  rw [h_sub] at h_dvd
  exact ⟨hnb.dvd_of_dvd_mul_left h_dvd, h_comp.2, h_comp.1⟩

/-- A Carmichael number (in the coprime Fermat pseudoprime formulation) is squarefree. -/
lemma squarefree_of_isCarmichael' {a : ℕ} (ha₂ : IsCarmichael' a) :
    Squarefree a := by
  have ha₁ : a.Composite := ⟨ha₂.1, ha₂.2.1⟩
  have ha₂_forall := ha₂.2.2
  simp_all [Nat.Composite, a.squarefree_iff_prime_squarefree, IsCarmichael', Nat.FermatPsp,
    Nat.ProbablePrime]
  rintro p hp ⟨N, rfl⟩
  apply absurd (ha₂_forall (p * N + 1) ((1).le_add_left _))
  have : Fact p.Prime := ⟨hp⟩
  rw [mul_assoc] at ha₁
  rw [mul_assoc, ← geom_sum_mul_of_one_le ((1).le_add_left (p * N)), p.coprime_mul_iff_left]
  simpa using (mul_dvd_mul_iff_right fun _ ↦ by simp_all only [mul_zero, not_lt_zero']).not.mpr
    ((ZMod.natCast_eq_zero_iff _ _).not.mp (by simp [le_of_lt ha₁.1]))

/-- Forward direction of Korselt's criterion from `IsCarmichael'`. -/
lemma korselt_forward {a : ℕ} (h : IsCarmichael' a) :
    ∀ p, p.Prime → p ∣ a → (p - 1 : ℕ) ∣ (a - 1 : ℕ) := by
  intro p hp hpa
  have ha₁ : a.Composite := ⟨h.1, h.2.1⟩
  have h_forall := h.2.2
  have : Fact p.Prime := ⟨hp⟩
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  obtain ⟨k, rfl⟩ := hpa
  have hk : k.Coprime p := by
    by_contra hk
    obtain ⟨_, rfl⟩ := not_not.1 <| hp.coprime_iff_not_dvd.not.1 <| mt Nat.Coprime.symm hk
    absurd (squarefree_of_isCarmichael' h)
    simp [← mul_assoc, mul_comm, Nat.squarefree_mul_iff, ← sq, Nat.squarefree_pow_iff hp.ne_one]
  simp_all [IsCarmichael', Nat.FermatPsp, Nat.ProbablePrime, Nat.Composite]
  let e : ZMod (p * k) ≃+* ZMod p × ZMod k := ZMod.chineseRemainder hk.symm
  let s : ZMod (p * k) := e.symm (g, 1)
  have : NeZero k := ⟨fun _ => by simp_all⟩
  have : p * k ∣ (e.symm (g, 1)).val ^ (p * k - 1) - 1 := h_forall _ (ZMod.val_pos.2 (by aesop))
    ((ZMod.isUnit_iff_coprime _ _).1 (by simp [Prod.isUnit_iff])).symm
  simp_all [p.totient_prime, sub_eq_zero, ZMod.val_pos, ← ZMod.natCast_eq_zero_iff,
    ← map_pow, ← Units.val_pow_eq_pow_val, ← orderOf_dvd_iff_pow_eq_one,
    orderOf_eq_card_of_forall_mem_zpowers]

/-- A composite number `a` is Carmichael if and only if it is squarefree
and, for all prime `p` dividing `a`, we have `p - 1 ∣ a - 1`. -/
theorem korselts_criterion (a : ℕ) (ha₁ : a.Composite) :
    IsCarmichael a ↔ Squarefree a ∧
      ∀ p, p.Prime → p ∣ a → (p - 1 : ℕ) ∣ (a - 1 : ℕ) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨ha₁, fun b ↦ ?_⟩⟩
  · have h' := isCarmichael'_of_isCarmichael h
    exact ⟨squarefree_of_isCarmichael' h', korselt_forward h'⟩
  · obtain ⟨h_sqfr, h_dvd⟩ := h
    simp_all [a.squarefree_iff_prime_squarefree, Nat.Composite]
    refine if hb : _ = 0 then ⟨0, hb⟩ else (a.factorization_le_iff_dvd ha₁.1.ne_bot hb).1 fun p => ?_
    by_cases hp : p.Prime
    · have : Fact p.Prime := ⟨hp⟩
      by_cases hpa : p ∣ a
      · obtain ⟨w, h⟩ := h_dvd p hp hpa
        obtain ⟨ha₁, ha₂⟩ := ha₁
        apply Nat.Prime.pow_dvd_iff_le_factorization hp hb |>.1
        have : a.factorization p ≤ 1 := not_lt.1 fun h =>
          h_sqfr p hp <| (sq p ▸ (pow_dvd_pow p h).trans (a.ordProj_dvd p))
        replace : a.factorization p = 1 :=
          this.antisymm (hp.dvd_iff_one_le_factorization (by grind) |>.1 hpa)
        simp_rw [this, pow_one, ← CharP.cast_eq_zero_iff (ZMod p)]
        have one_le_b_pow : b ≤ b ^ a := Nat.le_self_pow (by omega) b
        push_cast [one_le_b_pow]
        by_cases hbp : (b : ZMod p) = 0
        · have ha_pos : a ≠ 0 := by omega
          simp [hbp, ha_pos]
        · have h_sub : a = a - 1 + 1 := (Nat.sub_add_cancel (by omega)).symm
          rw [h_sub, h, pow_add, pow_mul, pow_one, ZMod.pow_card_sub_one_eq_one hbp]
          simp
      · simp [a.factorization_eq_zero_of_not_dvd hpa]
    · simp_all

lemma isCarmichael_of_isCarmichael' {n : ℕ} (h : IsCarmichael' n) : IsCarmichael n :=
  (korselts_criterion n ⟨h.1, h.2.1⟩).mpr ⟨squarefree_of_isCarmichael' h, korselt_forward h⟩

/-- The two formulations of Carmichael numbers are equivalent: `IsCarmichael n`
(requiring `n ∣ b^n - b` for all `b`) is equivalent to `IsCarmichael' n`
(requiring `n ∣ b^(n-1) - 1` for all `b` coprime to `n`). -/
theorem isCarmichael_iff_isCarmichael' {n : ℕ} :
    IsCarmichael n ↔ IsCarmichael' n :=
  ⟨isCarmichael'_of_isCarmichael, isCarmichael_of_isCarmichael'⟩
