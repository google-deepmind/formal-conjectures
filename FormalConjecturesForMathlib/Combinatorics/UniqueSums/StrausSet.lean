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

public import FormalConjecturesForMathlib.Combinatorics.UniqueSums.Dilation
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# Straus's simple set

This file develops Straus's simple set and the supporting material for the upper bound in Green's
Open Problem 27
(`green_27.variants.upper_be23`): every large prime `p` admits a set
`A ⊆ ZMod p` of size `O((log p)^2)` in which no element of `A + A` has a
unique representation.

The route is Łuczak–Schoen (Lemmas 4 and 5 of [LS08]) applied at `Q = 2`
to Straus's simple set [St76]:
`S = {0, ±⌊p/2⌋, ±⌊p/4⌋, …, ±1}` has `|S| ≤ 2 log₂ p + 1` and every element
of `S + S` has at least 2 ordered representations; a dilate `x₀ • S` with
`|S + x₀ • S| = |S|²` then gives a set where every sumset element has at
least 4 ≥ 3 representations.

References:
- [LS08] Łuczak, Tomasz and Schoen, Tomasz. "On the number of unique sums."
- [St76] Straus, E. G. "Differences of residues (mod p)." J. Number Theory 8 (1976) 40-42.
-/

open Finset
open scoped Pointwise

namespace UniqueSums

open Finset

variable {p : ℕ} [Fact p.Prime]

/--
Straus's *simple* set [St76, p. 41]: `{0, ±⌊p/2⌋, ±⌊p/4⌋, …, ±1}` in `ZMod p`,
written with `Nat.log 2 p` as the number of halvings.
-/
def strausSet (p : ℕ) : Finset (ZMod p) :=
  {0} ∪ (Finset.range (Nat.log 2 p)).image (fun j => ((p / 2 ^ (j + 1) : ℕ) : ZMod p))
    ∪ (Finset.range (Nat.log 2 p)).image (fun j => -((p / 2 ^ (j + 1) : ℕ) : ZMod p))

omit [Fact p.Prime] in
/--
The size bound for the simple set. The additive constant is necessary: the bound
`2 * Nat.log 2 p` without it fails at finite `p` (for example at `p = 257`).
-/
theorem strausSet_card_le : (strausSet p).card ≤ 2 * Nat.log 2 p + 1 := by
  unfold strausSet
  calc
    ({0} ∪ (Finset.range (Nat.log 2 p)).image
          (fun j ↦ ((p / 2 ^ (j + 1) : ℕ) : ZMod p)) ∪
        (Finset.range (Nat.log 2 p)).image
          (fun j ↦ -((p / 2 ^ (j + 1) : ℕ) : ZMod p))).card ≤
        ({0} : Finset (ZMod p)).card +
          ((Finset.range (Nat.log 2 p)).image
            (fun j ↦ ((p / 2 ^ (j + 1) : ℕ) : ZMod p))).card +
          ((Finset.range (Nat.log 2 p)).image
            (fun j ↦ -((p / 2 ^ (j + 1) : ℕ) : ZMod p))).card :=
      le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ ({0} : Finset (ZMod p)).card + (Finset.range (Nat.log 2 p)).card +
        (Finset.range (Nat.log 2 p)).card := by
      exact Nat.add_le_add
        (Nat.add_le_add_left Finset.card_image_le _)
        Finset.card_image_le
    _ = 2 * Nat.log 2 p + 1 := by simp; omega

/-- Explicit polynomial-versus-exponential bound. The base case `n = 26` is the
first point where the induction step's estimate closes; the exact value is
immaterial as this only feeds the asymptotic gate `strausSet_size_gate`. -/
private theorem eighty_one_mul_pow_four_lt_two_pow {n : ℕ} (hn : 26 ≤ n) :
    81 * n ^ 4 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hlin : 6 * (n + 1) ≤ 7 * n := by omega
      have hpow : (6 * (n + 1)) ^ 4 ≤ (7 * n) ^ 4 := Nat.pow_le_pow_left hlin 4
      simp only [mul_pow] at hpow
      norm_num at hpow
      have hnpos : 0 < n ^ 4 := pow_pos (by omega) 4
      have hpoly : (n + 1) ^ 4 < 2 * n ^ 4 := by omega
      calc
        81 * (n + 1) ^ 4 < 81 * (2 * n ^ 4) :=
          mul_lt_mul_of_pos_left hpoly (by norm_num)
        _ = (81 * n ^ 4) * 2 := by ring
        _ < (2 ^ n) * 2 := mul_lt_mul_of_pos_right ih (by norm_num)
        _ = 2 ^ (n + 1) := (Nat.pow_succ 2 n).symm

omit [Fact p.Prime] in
/--
The size hypothesis of `exists_dilate_card_add_eq` holds once `p ≥ 2^30`. The
threshold is chosen with slack: it forces `Nat.log 2 p ≥ 30`, comfortably above
the `n ≥ 26` needed for `81 * n ^ 4 < 2 ^ n`; any bound sufficient for large `p`
is enough here since the target statement is asymptotic.
-/
theorem strausSet_size_gate (hp : 2 ^ 30 ≤ p) :
    ((strausSet p).card ^ 2) ^ 2 < p := by
  let L := Nat.log 2 p
  have hp0 : p ≠ 0 := by omega
  have hL : 30 ≤ L := Nat.le_log_of_pow_le Nat.one_lt_two hp
  have honeL : 1 ≤ L := by omega
  have hlinear : 2 * L + 1 ≤ 3 * L := by omega
  have hpoly : (2 * L + 1) ^ 4 ≤ 81 * L ^ 4 := by
    calc
      (2 * L + 1) ^ 4 ≤ (3 * L) ^ 4 := Nat.pow_le_pow_left hlinear 4
      _ = 81 * L ^ 4 := by norm_num [mul_pow]
  have hcard : (strausSet p).card ^ 4 ≤ (2 * L + 1) ^ 4 :=
    Nat.pow_le_pow_left strausSet_card_le 4
  calc
    ((strausSet p).card ^ 2) ^ 2 = (strausSet p).card ^ 4 := by ring
    _ ≤ (2 * L + 1) ^ 4 := hcard
    _ ≤ 81 * L ^ 4 := hpoly
    _ < 2 ^ L := eighty_one_mul_pow_four_lt_two_pow (by omega)
    _ ≤ p := Nat.pow_log_le_self 2 hp0

omit [Fact p.Prime] in
theorem natLog_sq_bound (hp : 2 ≤ p) :
    (2 * (Nat.log 2 p : ℝ) + 1) ^ 2 ≤ 36 * (Real.log (p : ℝ)) ^ 2 := by
  let L := Nat.log 2 p
  have hp0 : p ≠ 0 := by omega
  have hL : 1 ≤ L := Nat.le_log_of_pow_le Nat.one_lt_two (by simpa using hp)
  have hpow : 2 ^ L ≤ p := Nat.pow_log_le_self 2 hp0
  have hpowR : (2 : ℝ) ^ L ≤ (p : ℝ) := by exact_mod_cast hpow
  have hlogpow : Real.log ((2 : ℝ) ^ L) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow] at hlogpow
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hhalfL : (L : ℝ) / 2 ≤ (L : ℝ) * Real.log 2 := by
    calc
      (L : ℝ) / 2 = (L : ℝ) * (1 / 2) := by ring
      _ ≤ (L : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hlogtwo (by positivity)
  have hLlog : (L : ℝ) ≤ 2 * Real.log (p : ℝ) := by linarith
  have hlinear : 2 * (L : ℝ) + 1 ≤ 3 * (L : ℝ) := by norm_cast; omega
  have hlog_nonneg : 0 ≤ Real.log (p : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ p by omega)
  nlinarith [sq_nonneg (2 * (Nat.log 2 p : ℝ) + 1),
    sq_nonneg (3 * (Nat.log 2 p : ℝ)), sq_nonneg (6 * Real.log (p : ℝ))]

omit [Fact p.Prime] in
theorem two_le_strausSet_card (hp : 5 ≤ p) : 2 ≤ (strausSet p).card := by
  have hlog : 1 ≤ Nat.log 2 p :=
    Nat.le_log_of_pow_le Nat.one_lt_two (by norm_num; omega)
  let v : ZMod p := (p / 2 : ℕ)
  have hzero : (0 : ZMod p) ∈ strausSet p := by
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self 0))
  have hv : v ∈ strausSet p := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨0, by simpa only [Finset.mem_range] using hlog, by simp [v]⟩
  have hvpos : 0 < p / 2 := Nat.div_pos (by omega) (by omega)
  have hvlt : p / 2 < p := Nat.div_lt_self (by omega) (by omega)
  have hvne : v ≠ 0 := by
    dsimp only [v]
    intro hz
    exact Nat.not_dvd_of_pos_of_lt hvpos hvlt
      ((ZMod.natCast_eq_zero_iff (p / 2) p).mp hz)
  exact Finset.one_lt_card_iff.mpr ⟨0, v, hzero, hv, hvne.symm⟩

omit [Fact p.Prime] in
private theorem minRep_two_of_double_reps {S : Finset (ZMod p)}
    (hdouble : ∀ s ∈ S, ∃ u ∈ S, ∃ v ∈ S, u + v = s + s ∧ (u, v) ≠ (s, s)) :
    MinRep S 2 := by
  intro g hg
  rcases Finset.mem_add.mp hg with ⟨s, hs, t, ht, hst⟩
  change 2 ≤ ((S ×ˢ S).filter fun q ↦ q.1 + q.2 = g).card
  have hpair : (s, t) ∈ (S ×ˢ S).filter (fun q ↦ q.1 + q.2 = g) := by
    simp only [Finset.mem_filter, Finset.mem_product, hs, ht, hst, and_self]
  by_cases heq : s = t
  · subst t
    rcases hdouble s hs with ⟨u, hu, v, hv, huv, hne⟩
    have huvpair : (u, v) ∈ (S ×ˢ S).filter (fun q ↦ q.1 + q.2 = g) := by
      simp only [Finset.mem_filter, Finset.mem_product, hu, hv, true_and]
      exact huv.trans hst
    have hone : 1 < ((S ×ˢ S).filter fun q ↦ q.1 + q.2 = g).card :=
      Finset.one_lt_card_iff.mpr ⟨(s, s), (u, v), hpair, huvpair, hne.symm⟩
    omega
  · have hswap : (t, s) ∈ (S ×ˢ S).filter (fun q ↦ q.1 + q.2 = g) := by
      simp only [Finset.mem_filter, Finset.mem_product, ht, hs, true_and]
      rw [add_comm]
      exact hst
    have hpairs_ne : (s, t) ≠ (t, s) := by
      intro h
      exact heq (congrArg Prod.fst h)
    have hone : 1 < ((S ×ˢ S).filter fun q ↦ q.1 + q.2 = g).card :=
      Finset.one_lt_card_iff.mpr ⟨(s, t), (t, s), hpair, hswap, hpairs_ne⟩
    omega

/--
Every element of `S + S` has at least 2 ordered representations: `S = -S`, so
differences of members are sums, and the floor-doubling identity
`2 * (p / 2 ^ (j + 1)) = p / 2 ^ j - ε` with `ε ∈ {0, 1}` provides every doubled
element a second representation.
-/
theorem minRep_strausSet_two (hp : 5 ≤ p) : MinRep (strausSet p) 2 := by
  let L := Nat.log 2 p
  have hp0 : p ≠ 0 := by omega
  have hLpos : 0 < L := by
    exact Nat.log_pos Nat.one_lt_two (by omega)
  have hpowL : 2 ^ L ≤ p := by
    exact Nat.pow_log_le_self 2 hp0
  have htop : p / 2 ^ L = 1 := by
    apply Nat.div_eq_of_lt_le
    · simpa only [one_mul] using hpowL
    · have hlt : p < 2 ^ L * 2 := by
        simpa only [L, Nat.pow_succ] using Nat.lt_pow_succ_log_self Nat.one_lt_two p
      simpa only [Nat.reduceAdd, Nat.mul_comm] using hlt
  have hpos_exp {e : ℕ} (he0 : 0 < e) (heL : e ≤ L) :
      ((p / 2 ^ e : ℕ) : ZMod p) ∈ strausSet p := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨e - 1, ?_, ?_⟩
    · simpa only [Finset.mem_range] using (show e - 1 < L by omega)
    · rw [Nat.sub_add_cancel he0]
  have hneg_exp {e : ℕ} (he0 : 0 < e) (heL : e ≤ L) :
      -((p / 2 ^ e : ℕ) : ZMod p) ∈ strausSet p := by
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨e - 1, ?_, ?_⟩
    · simpa only [Finset.mem_range] using (show e - 1 < L by omega)
    · rw [Nat.sub_add_cancel he0]
  have hzero : (0 : ZMod p) ∈ strausSet p := by
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self 0))
  have hone : (1 : ZMod p) ∈ strausSet p := by
    simpa only [htop, Nat.cast_one] using hpos_exp hLpos le_rfl
  have hnegone : (-1 : ZMod p) ∈ strausSet p := by
    simpa only [htop, Nat.cast_one] using hneg_exp hLpos le_rfl
  have hterm_pos {e : ℕ} (he0 : 0 < e) (heL : e ≤ L) : 0 < p / 2 ^ e := by
    apply Nat.div_pos
    · exact (Nat.pow_le_pow_right (by omega) heL).trans hpowL
    · exact Nat.pow_pos (by omega)
  have hterm_lt {e : ℕ} (he0 : 0 < e) : p / 2 ^ e < p := by
    exact Nat.div_lt_self (by omega) (Nat.one_lt_pow (by omega) Nat.one_lt_two)
  have hterm_ne_zero {e : ℕ} (he0 : 0 < e) (heL : e ≤ L) :
      ((p / 2 ^ e : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    exact Nat.not_dvd_of_pos_of_lt (hterm_pos he0 heL) (hterm_lt he0)
      ((ZMod.natCast_eq_zero_iff (p / 2 ^ e) p).mp hz)
  have hneg_closed : ∀ x ∈ strausSet p, -x ∈ strausSet p := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · rw [Finset.mem_singleton] at hx
        subst x
        simpa only [neg_zero] using hzero
      · rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
        exact hneg_exp (by omega)
          (by dsimp only [L]; exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hj))
    · rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
      simpa only [neg_neg] using hpos_exp (by omega)
        (by dsimp only [L]; exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hj))
  have hpositive (j : ℕ) (hj : j < L) :
      ∃ u ∈ strausSet p, ∃ v ∈ strausSet p,
        u + v = ((p / 2 ^ (j + 1) : ℕ) : ZMod p) +
          ((p / 2 ^ (j + 1) : ℕ) : ZMod p) ∧
        (u, v) ≠ (((p / 2 ^ (j + 1) : ℕ) : ZMod p),
          ((p / 2 ^ (j + 1) : ℕ) : ZMod p)) := by
    let n := p / 2 ^ (j + 1)
    have hnpos : 0 < n := hterm_pos (by omega) (by omega)
    have hnlt : n < p := hterm_lt (by omega)
    have hnne : (n : ZMod p) ≠ 0 := hterm_ne_zero (by omega) (by omega)
    by_cases hj0 : j = 0
    · subst j
      have hpmod : p % 2 = 1 :=
        (Fact.out : Nat.Prime p).mod_two_eq_one_iff_ne_two.mpr (by omega)
      have hnat : 2 * n + 1 = p := by
        dsimp only [n]
        have hdiv := Nat.div_add_mod p 2
        omega
      have hz : (n : ZMod p) + (n : ZMod p) + 1 = 0 := by
        calc
          (n : ZMod p) + (n : ZMod p) + 1 = ((2 * n + 1 : ℕ) : ZMod p) := by
            norm_num [two_mul]
          _ = (p : ℕ) := congrArg (fun m : ℕ ↦ (m : ZMod p)) hnat
          _ = 0 := ZMod.natCast_self p
      refine ⟨0, hzero, -1, hnegone, ?_, ?_⟩
      · apply add_right_cancel (b := (1 : ZMod p))
        simpa only [zero_add, neg_add_cancel] using hz.symm
      · intro heq
        exact hnne (congrArg Prod.fst heq).symm
    · let q := p / 2 ^ j
      have hjpos : 0 < j := by omega
      have hqmem : (q : ZMod p) ∈ strausSet p := hpos_exp hjpos (by omega)
      have hqpos : 0 < q := hterm_pos hjpos (by omega)
      have hqlt : q < p := hterm_lt hjpos
      have hndiv : n = q / 2 := by
        dsimp only [n, q]
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      have hqne : (q : ZMod p) ≠ (n : ZMod p) := by
        intro heq
        have hval := congrArg ZMod.val heq
        rw [ZMod.val_cast_of_lt hqlt, ZMod.val_cast_of_lt hnlt] at hval
        have hdiv := Nat.div_add_mod q 2
        omega
      rcases Nat.mod_two_eq_zero_or_one q with hmod | hmod
      · have hnat : 2 * n = q := by
          have hdiv := Nat.div_add_mod q 2
          omega
        refine ⟨q, hqmem, 0, hzero, ?_, ?_⟩
        · calc
            (q : ZMod p) + 0 = (q : ZMod p) := add_zero _
            _ = ((2 * n : ℕ) : ZMod p) :=
              congrArg (fun m : ℕ ↦ (m : ZMod p)) hnat.symm
            _ = (n : ZMod p) + (n : ZMod p) := by norm_num [two_mul]
        · intro heq
          exact hqne (congrArg Prod.fst heq)
      · have hnat : 2 * n + 1 = q := by
          have hdiv := Nat.div_add_mod q 2
          omega
        refine ⟨q, hqmem, -1, hnegone, ?_, ?_⟩
        · apply add_right_cancel (b := (1 : ZMod p))
          calc
            ((q : ZMod p) + -1) + 1 = (q : ZMod p) := by simp
            _ = ((2 * n + 1 : ℕ) : ZMod p) :=
              congrArg (fun m : ℕ ↦ (m : ZMod p)) hnat.symm
            _ = ((n : ZMod p) + (n : ZMod p)) + 1 := by norm_num [two_mul]
        · intro heq
          exact hqne (congrArg Prod.fst heq)
  apply minRep_two_of_double_reps
  intro s hs
  rcases Finset.mem_union.mp hs with hs | hs
  · rcases Finset.mem_union.mp hs with hs | hs
    · rw [Finset.mem_singleton] at hs
      subst s
      refine ⟨1, hone, -1, hnegone, by simp, ?_⟩
      intro heq
      exact one_ne_zero (congrArg Prod.fst heq)
    · rcases Finset.mem_image.mp hs with ⟨j, hj, rfl⟩
      exact hpositive j (by simpa only [L] using Finset.mem_range.mp hj)
  · rcases Finset.mem_image.mp hs with ⟨j, hj, rfl⟩
    rcases hpositive j (by simpa only [L] using Finset.mem_range.mp hj) with
      ⟨u, hu, v, hv, huv, hne⟩
    refine ⟨-u, hneg_closed u hu, -v, hneg_closed v hv, ?_, ?_⟩
    · simpa only [neg_add_rev, add_comm] using congrArg Neg.neg huv
    · intro heq
      apply hne
      apply Prod.ext
      · exact neg_injective (congrArg Prod.fst heq)
      · exact neg_injective (congrArg Prod.snd heq)

/--
The `Q = 2` combine: for `(|S|²)² < p`, the set `A = S + x₀ • S` given by Lemma 4
has `|A| = |S|² ≤ (2 log₂ p + 1)²` and, by Lemma 5, `MinRep A 4`, hence no unique
representations. This is the finite-`p` content of `upper_be23`.
-/
theorem exists_hasNoUniqueRepresentation_card_le
    (hp : 5 ≤ p) (hsize : ((strausSet p).card ^ 2) ^ 2 < p) :
    ∃ A : Finset (ZMod p), 2 ≤ A.card ∧ HasNoUniqueRepresentation A ∧
      A.card ≤ (2 * Nat.log 2 p + 1) ^ 2 := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let S := strausSet p
  have hScard : 2 ≤ S.card := two_le_strausSet_card hp
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hsmall : (S.card * S.card) ^ 2 < p := by
    simpa only [S, pow_two] using hsize
  rcases exists_dilate_card_add_eq hsmall hSne hSne with ⟨x, hx, hcard⟩
  have hxcoprime : Nat.Coprime x.val p := by
    apply Nat.Coprime.symm
    apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
    intro hdiv
    apply hx
    rw [← ZMod.natCast_zmod_val x, ZMod.natCast_eq_zero_iff x.val p]
    exact hdiv
  have hxunit : IsUnit x := by
    rw [← ZMod.natCast_zmod_val x]
    exact (ZMod.isUnit_iff_coprime x.val p).mpr hxcoprime
  have hmul : Function.Injective (x * ·) := hxunit.mul_right_injective
  let T := S.image (x * ·)
  have hSmin : MinRep S 2 := minRep_strausSet_two hp
  have hTmin : MinRep T 2 := by
    exact minRep_image_mul hmul hSmin
  have hcardST : (S + T).card = S.card * S.card := by
    simpa only [T] using hcard
  have hTcard : T.card = S.card := by
    simpa only [T] using Finset.card_image_of_injective S hmul
  have hcardST' : (S + T).card = S.card * T.card := by
    rw [hTcard]
    exact hcardST
  have hsum4 : MinRep (S + T) 4 := by
    simpa only [Nat.reduceMul] using Finset.MinRep.add hSmin hTmin hcardST'
  have hsum3 : MinRep (S + T) 3 := by
    intro g hg
    exact Nat.le_trans (by omega : 3 ≤ 4) (hsum4 g hg)
  refine ⟨S + T, ?_, Finset.hasNoUniqueRepresentation_of_minRep_three hsum3, ?_⟩
  · rw [hcardST]
    have hfour : 4 ≤ S.card * S.card := by
      simpa only [Nat.reduceMul] using Nat.mul_le_mul hScard hScard
    omega
  · rw [hcardST]
    have hbound := Nat.mul_le_mul (strausSet_card_le (p := p)) (strausSet_card_le (p := p))
    simpa only [S, pow_two] using hbound

end UniqueSums
