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

public import FormalConjecturesForMathlib.Computability.SearchProblems
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Number-theoretic decision and search problems

All integer parameters use the existing binary encodings, not unary bounds or
multiplication tables. Factors of an RSA modulus are quantified in its promise;
they are not part of the algorithm's input.

Sources:
* Garey and Johnson, *Computers and Intractability* (1979), AN1, p. 249, and AN8,
  p. 250: positive inputs and strictly positive witnesses.
* Menezes, van Oorschot, and Vanstone, *Handbook of Applied Cryptography* (1996),
  Definitions 3.28, 3.31, and 3.51, pp. 98, 99, 103:
  https://cacr.uwaterloo.ca/hac/about/chap3.pdf.

Finite quantifiers below give exhaustive reference checks, not polynomial-time
algorithms. The equivalence lemmas connect them to unrestricted arithmetic witnesses
and to Mathlib's actual residue rings and primitive roots.
-/

@[expose] public section

namespace NumberTheoryProblems

/-- Binary-encoded parameters $(a,b,c)$ for the two quadratic decision problems. -/
abbrev QuadraticInput := ℕ × ℕ × ℕ

/-- AN1: a positive root strictly below $c$ of $x^2 \equiv a \pmod b$.
An input with a zero parameter is rejected. -/
def BoundedQuadraticCongruence (i : QuadraticInput) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ 0 < i.2.2 ∧
    ∃ x : Fin i.2.2, 0 < x.val ∧ x.val ^ 2 % i.2.1 = i.1 % i.2.1

instance (i : QuadraticInput) : Decidable (BoundedQuadraticCongruence i) := by
  unfold BoundedQuadraticCongruence
  infer_instance

theorem boundedQuadraticCongruence_iff (i : QuadraticInput) :
    BoundedQuadraticCongruence i ↔
      0 < i.1 ∧ 0 < i.2.1 ∧ 0 < i.2.2 ∧
        ∃ x : ℕ, 0 < x ∧ x < i.2.2 ∧ x ^ 2 ≡ i.1 [MOD i.2.1] := by
  simp only [BoundedQuadraticCongruence, Nat.ModEq]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun ⟨x, hx, heq⟩ ↦ ⟨x.val, hx, x.isLt, heq⟩,
      fun ⟨x, hx, hlt, heq⟩ ↦ ⟨⟨x, hlt⟩, hx, heq⟩⟩

/-- AN8: positive solutions to $a x^2 + b y = c$, with positive $a,b,c$.
The witness bounds follow from the equation and positivity. -/
def BinaryQuadraticDiophantine (i : QuadraticInput) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ 0 < i.2.2 ∧
    ∃ x y : Fin (i.2.2 + 1), 0 < x.val ∧ 0 < y.val ∧
      i.1 * x.val ^ 2 + i.2.1 * y.val = i.2.2

instance (i : QuadraticInput) : Decidable (BinaryQuadraticDiophantine i) := by
  unfold BinaryQuadraticDiophantine
  infer_instance

theorem binaryQuadraticDiophantine_iff (i : QuadraticInput) :
    BinaryQuadraticDiophantine i ↔
      0 < i.1 ∧ 0 < i.2.1 ∧ 0 < i.2.2 ∧
        ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ i.1 * x ^ 2 + i.2.1 * y = i.2.2 := by
  refine and_congr_right fun ha ↦ and_congr_right fun hb ↦ and_congr_right fun _ ↦ ?_
  constructor
  · rintro ⟨x, y, hx, hy, heq⟩
    exact ⟨x.val, y.val, hx, hy, heq⟩
  · rintro ⟨x, y, hx, hy, heq⟩
    have hxx : x ≤ x ^ 2 := Nat.le_self_pow (by decide) x
    have hax : x ^ 2 ≤ i.1 * x ^ 2 := Nat.le_mul_of_pos_left _ ha
    have hby : y ≤ i.2.1 * y := Nat.le_mul_of_pos_left _ hb
    exact ⟨⟨x, by omega⟩, ⟨y, by omega⟩, hx, hy, heq⟩

/-- The modulus and a signed representative of a residue class. -/
abbrev ResiduosityInput := ℕ × ℤ

/-- An odd composite modulus and Jacobi symbol one. Moduli zero and one are excluded. -/
def ResiduosityPromise (i : ResiduosityInput) : Prop :=
  3 ≤ i.1 ∧ i.1 % 2 = 1 ∧ ¬ i.1.Prime ∧ jacobiSym i.2 i.1 = 1

instance (i : ResiduosityInput) : Decidable (ResiduosityPromise i) := by
  unfold ResiduosityPromise
  infer_instance

/-- The promised Jacobi value implies that the residue represents a unit. -/
theorem ResiduosityPromise.coprime {i : ResiduosityInput} (h : ResiduosityPromise i) :
    i.2.gcd (i.1 : ℤ) = 1 := by
  let : NeZero i.1 := ⟨by have := h.1; omega⟩
  by_contra hc
  have hz := jacobiSym.eq_zero_iff_not_coprime.mpr hc
  rw [h.2.2.2] at hz
  contradiction

/-- A square root among the complete set of canonical residues, including zero. -/
def IsQuadraticResidue (i : ResiduosityInput) : Prop :=
  ∃ x : Fin i.1, (x.val : ℤ) ^ 2 % i.1 = i.2 % i.1

instance (i : ResiduosityInput) : Decidable (IsQuadraticResidue i) := by
  unfold IsQuadraticResidue
  infer_instance

theorem isQuadraticResidue_iff (i : ResiduosityInput) (hn : 0 < i.1) :
    IsQuadraticResidue i ↔ IsSquare (i.2 : ZMod i.1) := by
  let : NeZero i.1 := ⟨hn.ne'⟩
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(x.val : ZMod i.1), ?_⟩
    have h := (ZMod.intCast_eq_intCast_iff' _ _ i.1).mpr hx
    simpa [sq] using h.symm
  · rintro ⟨x, hx⟩
    refine ⟨⟨x.val, ZMod.val_lt x⟩, ?_⟩
    apply (ZMod.intCast_eq_intCast_iff' _ _ i.1).mp
    simpa [sq, ZMod.natCast_zmod_val] using hx.symm

/-- The public input $(n,e,c)$, with a signed ciphertext representative. -/
abbrev RSAInput := ℕ × ℕ × ℤ

/-- RSA's two distinct odd prime factors are hidden mathematical witnesses, not input data. -/
def RSAPromise (i : RSAInput) : Prop :=
  0 < i.2.1 ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % 2 = 1 ∧ q % 2 = 1 ∧
    p ≠ q ∧ i.1 = p * q ∧ i.2.1.Coprime ((p - 1) * (q - 1))

/-- A finite reference check for the promise; the bounds follow from the prime factors. -/
theorem rsaPromise_iff_bounded (i : RSAInput) :
    RSAPromise i ↔ 0 < i.2.1 ∧ ∃ p q : Fin (i.1 + 1),
      p.val.Prime ∧ q.val.Prime ∧ p.val % 2 = 1 ∧ q.val % 2 = 1 ∧
        p.val ≠ q.val ∧ i.1 = p.val * q.val ∧
          i.2.1.Coprime ((p.val - 1) * (q.val - 1)) := by
  refine and_congr_right fun _ ↦ ?_
  constructor
  · rintro ⟨p, q, hp, hq, hop, hoq, hne, hn, hcop⟩
    have hpn : p ≤ i.1 := hn ▸ Nat.le_mul_of_pos_right p hq.pos
    have hqn : q ≤ i.1 := hn ▸ Nat.le_mul_of_pos_left q hp.pos
    exact ⟨⟨p, by omega⟩, ⟨q, by omega⟩, hp, hq, hop, hoq, hne, hn, hcop⟩
  · rintro ⟨p, q, hp, hq, hop, hoq, hne, hn, hcop⟩
    exact ⟨p.val, q.val, hp, hq, hop, hoq, hne, hn, hcop⟩

instance (i : RSAInput) : Decidable (RSAPromise i) :=
  decidable_of_iff _ (rsaPromise_iff_bounded i).symm

/-- Return a canonical $e$-th root. Nonunit ciphertexts are allowed. -/
def RSAOutput (i : RSAInput) (m : ℕ) : Prop :=
  m < i.1 ∧ (m : ℤ) ^ i.2.1 % i.1 = i.2.2 % i.1

instance (i : RSAInput) (m : ℕ) : Decidable (RSAOutput i m) := by
  unfold RSAOutput
  infer_instance

theorem rsaOutput_iff (i : RSAInput) (m : ℕ) :
    RSAOutput i m ↔ m < i.1 ∧ (m : ZMod i.1) ^ i.2.1 = (i.2.2 : ZMod i.1) := by
  simp only [RSAOutput, ← ZMod.intCast_eq_intCast_iff', Int.cast_pow, Int.cast_natCast]

private theorem primeField_pow_surjective {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hcop : e.Coprime (p - 1)) : Function.Surjective (fun x : ZMod p ↦ x ^ e) := by
  let : Fact p.Prime := ⟨hp⟩
  intro c
  by_cases hc : c = 0
  · exact ⟨0, by simp [hc, he.ne']⟩
  have hcard : (Nat.card (ZMod p)ˣ).Coprime e := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using hcop.symm
  obtain ⟨m, hm⟩ := hcard.pow_left_bijective.2 (Units.mk0 c hc)
  exact ⟨m.val, congrArg Units.val hm⟩

private theorem rsa_pow_bijective {p q e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (he : 0 < e) (hcop : e.Coprime ((p - 1) * (q - 1))) :
    Function.Bijective (fun x : ZMod (p * q) ↦ x ^ e) := by
  let : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  let crt := ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr hpq)
  obtain ⟨hep, heq⟩ := Nat.coprime_mul_iff_right.mp hcop
  have hs : Function.Surjective (fun x : ZMod (p * q) ↦ x ^ e) := by
    intro c
    obtain ⟨a, ha⟩ := primeField_pow_surjective hp he hep (crt c).1
    obtain ⟨b, hb⟩ := primeField_pow_surjective hq he heq (crt c).2
    refine ⟨crt.symm (a, b), crt.injective ?_⟩
    rw [map_pow, crt.apply_symm_apply]
    exact Prod.ext ha hb
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

/-- RSA's promise makes exponentiation a permutation on all residues, not just units. -/
theorem existsUnique_rsaOutput (i : RSAInput) (h : RSAPromise i) : ∃! m, RSAOutput i m := by
  obtain ⟨n, e, c⟩ := i
  obtain ⟨he, p, q, hp, hq, _, _, hpq, rfl, hcop⟩ := h
  let : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  obtain ⟨m, hm, hu⟩ := (rsa_pow_bijective hp hq hpq he hcop).existsUnique (c : ZMod (p * q))
  refine ⟨m.val, (rsaOutput_iff _ _).mpr ⟨ZMod.val_lt m, ?_⟩, ?_⟩
  · simpa only [ZMod.natCast_zmod_val] using hm
  · intro y hy
    obtain ⟨hy, hye⟩ := (rsaOutput_iff _ _).mp hy
    have hm := congrArg ZMod.val (hu (y : ZMod (p * q)) hye)
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hy] using hm

/-- Binary-encoded $(p,g,b)$, not an explicitly tabulated finite group. -/
abbrev DiscreteLogarithmInput := ℕ × ℕ × ℕ

/-- A prime modulus, canonical nonzero base and target, and a primitive base.
The last clause tests all positive exponents below $p-1$. -/
def DiscreteLogarithmPromise (i : DiscreteLogarithmInput) : Prop :=
  i.1.Prime ∧ 0 < i.2.1 ∧ i.2.1 < i.1 ∧ 0 < i.2.2 ∧ i.2.2 < i.1 ∧
    ∀ k : Fin (i.1 - 1), 0 < k.val → i.2.1 ^ k.val % i.1 ≠ 1

instance (i : DiscreteLogarithmInput) : Decidable (DiscreteLogarithmPromise i) := by
  unfold DiscreteLogarithmPromise
  infer_instance

/-- Return the exponent in $[0,p-2]$, including zero for the target one. -/
def DiscreteLogarithmOutput (i : DiscreteLogarithmInput) (x : ℕ) : Prop :=
  x < i.1 - 1 ∧ i.2.1 ^ x % i.1 = i.2.2

instance (i : DiscreteLogarithmInput) (x : ℕ) :
    Decidable (DiscreteLogarithmOutput i x) := by
  unfold DiscreteLogarithmOutput
  infer_instance

/-- The finite exponent test expresses an actual primitive root in the prime field. -/
theorem discreteLogarithmPromise_iff (i : DiscreteLogarithmInput) :
    DiscreteLogarithmPromise i ↔
      i.1.Prime ∧ 0 < i.2.1 ∧ i.2.1 < i.1 ∧ 0 < i.2.2 ∧ i.2.2 < i.1 ∧
        IsPrimitiveRoot (i.2.1 : ZMod i.1) (i.1 - 1) := by
  refine and_congr_right fun hp ↦ and_congr_right fun hg ↦ and_congr_right fun hgp ↦
    and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  let : Fact i.1.Prime := ⟨hp⟩
  have hg0 : (i.2.1 : ZMod i.1) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hgp]
      using hg.ne'
  constructor
  · intro h
    refine IsPrimitiveRoot.mk_of_lt _ (by omega) (ZMod.pow_card_sub_one_eq_one hg0) ?_
    intro k hk hkp heq
    apply h ⟨k, hkp⟩ hk
    have hm := (ZMod.natCast_eq_natCast_iff' (i.2.1 ^ k) 1 i.1).mp (by simpa using heq)
    simpa [Nat.mod_eq_of_lt hp.one_lt] using hm
  · intro h k hk heq
    apply h.pow_ne_one_of_pos_of_lt hk.ne' k.isLt
    have hm := (ZMod.natCast_eq_natCast_iff' (i.2.1 ^ k.val) 1 i.1).mpr
      (by simpa [Nat.mod_eq_of_lt hp.one_lt] using heq)
    simpa using hm

theorem discreteLogarithmOutput_iff (i : DiscreteLogarithmInput) (hb : i.2.2 < i.1)
    (x : ℕ) :
    DiscreteLogarithmOutput i x ↔
      x < i.1 - 1 ∧ (i.2.1 : ZMod i.1) ^ x = (i.2.2 : ZMod i.1) := by
  unfold DiscreteLogarithmOutput
  refine and_congr_right fun _ ↦ ?_
  simpa only [Nat.cast_pow, Nat.mod_eq_of_lt hb] using
    (ZMod.natCast_eq_natCast_iff' (i.2.1 ^ x) i.2.2 i.1).symm

/-- Every promised discrete-logarithm input has exactly one canonical output. -/
theorem existsUnique_discreteLogarithmOutput (i : DiscreteLogarithmInput)
    (h : DiscreteLogarithmPromise i) : ∃! x, DiscreteLogarithmOutput i x := by
  obtain ⟨hp, _, _, hb, hbp, hg⟩ := (discreteLogarithmPromise_iff i).mp h
  let : Fact i.1.Prime := ⟨hp⟩
  let : NeZero (i.1 - 1) := ⟨by have := hp.two_le; omega⟩
  have hb0 : (i.2.2 : ZMod i.1) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hbp]
      using hb.ne'
  obtain ⟨x, hx, hpow⟩ := hg.eq_pow_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hb0)
  refine ⟨x, (discreteLogarithmOutput_iff i hbp x).mpr ⟨hx, hpow⟩, ?_⟩
  intro y hy
  obtain ⟨hy, hypow⟩ := (discreteLogarithmOutput_iff i hbp y).mp hy
  exact hg.pow_inj hy hx (hypow.trans hpow.symm)

end NumberTheoryProblems
