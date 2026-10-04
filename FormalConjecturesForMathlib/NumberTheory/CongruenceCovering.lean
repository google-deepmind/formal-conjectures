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

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic

/-!
# The minimum density of a finite congruence covering

*Reference:* [erdosproblems.com/278](https://www.erdosproblems.com/278)

Let `n : ι → ℕ` be a finite family of positive moduli and `a : ι → ℤ` a choice of residues.
An integer `x` is *covered* if `x ≡ a i (mod n i)` for some `i`.

We prove the settled part of Erdős Problem 278: the natural density of the set of covered
integers exists, it is minimized when all residues are equal (here: all `0`), and the
minimum value is the inclusion–exclusion sum
`∑_{∅ ≠ S} (-1)^(|S|+1) / lcm(n_i : i ∈ S)`.

The proof is a prime-by-prime compression: for `L = p^k * M`, replacing every residue `a i`
by `a i * e` (with `e ≡ 0 mod p^k`, `e ≡ 1 mod M`) never increases the number of covered
residues mod `L`, because the subgroups of `ℤ/p^k` form a chain.

The first question of the problem (the *maximum* density) is open and is not formalized here.
-/

@[expose] public section

open Finset Filter Topology

namespace CongruenceCovering

variable {ι : Type*} [Fintype ι]

/-- `x` is covered by the system of congruences `x ≡ a i (mod n i)`. -/
def Covered (n : ι → ℕ) (a : ι → ℤ) (x : ℤ) : Prop := ∃ i, x ≡ a i [ZMOD n i]

open scoped Classical in
/-- Number of covered integers in `{0, …, L-1}`. -/
noncomputable def coverCount (L : ℕ) (n : ι → ℕ) (a : ι → ℤ) : ℕ :=
  ((Finset.range L).filter (fun x : ℕ => Covered n a x)).card

open scoped Classical in
/-- A set `s ⊆ ℕ` has natural density `δ`. -/
def HasNatDensity (s : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (((Finset.range N).filter (· ∈ s)).card : ℝ) / N) atTop (𝓝 δ)

open scoped Classical

/-! ### The compression step at one prime -/

lemma coverCount_compress {L q M p k : ℕ} (hp : p.Prime) (hq : q = p ^ k)
    (hcop : q.Coprime M) (hL : L = q * M) (n : ι → ℕ) (hn : ∀ i, n i ∣ L)
    (e : ℤ) (he0 : (q : ℤ) ∣ e) (he1 : e ≡ 1 [ZMOD M]) (a : ι → ℤ) :
    coverCount L n (fun i => a i * e) ≤ coverCount L n a := by
  subst hq
  set gq : ι → ℕ := fun i => (n i).gcd (p ^ k) with hgqdef
  set gM : ι → ℕ := fun i => (n i).gcd M with hgMdef
  have hgq : ∀ i, gq i ∣ p ^ k := fun i => Nat.gcd_dvd_right _ _
  have hgM : ∀ i, gM i ∣ M := fun i => Nat.gcd_dvd_right _ _
  have hqL : (p ^ k : ℕ) ∣ L := ⟨M, hL⟩
  have hML : M ∣ L := ⟨p ^ k, by rw [hL, mul_comm]⟩
  have hsplit : ∀ i (x b : ℤ), x ≡ b [ZMOD n i] ↔ x ≡ b [ZMOD gq i] ∧ x ≡ b [ZMOD gM i] := by
    intro i x b
    have hni : n i = gq i * gM i := by
      have := Nat.Coprime.gcd_mul (n i) hcop
      rw [← hL, Nat.gcd_eq_left (hn i)] at this
      exact this
    have hc : (gq i).Coprime (gM i) :=
      (hcop.coprime_dvd_left (hgq i)).coprime_dvd_right (hgM i)
    rw [hni, Nat.cast_mul]
    exact (Int.modEq_and_modEq_iff_modEq_mul (m := (gq i : ℤ)) (n := (gM i : ℤ))
      (by simpa using hc)).symm
  have hchain : ∀ i j, gq i ≤ gq j → gq i ∣ gq j := by
    intro i j hij
    obtain ⟨a1, -, h1⟩ := (Nat.dvd_prime_pow hp).1 (hgq i)
    obtain ⟨a2, -, h2⟩ := (Nat.dvd_prime_pow hp).1 (hgq j)
    rw [h1, h2] at hij ⊢
    exact Nat.pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).1 hij)
  set e' : ℤ := 1 - e with he'def
  have he0' : e ≡ 0 [ZMOD (p ^ k : ℕ)] := Int.modEq_zero_iff_dvd.2 he0
  have he'1 : e' ≡ 1 [ZMOD (p ^ k : ℕ)] := by
    simpa using (Int.ModEq.refl (1 : ℤ)).sub he0'
  have he'0 : e' ≡ 0 [ZMOD M] := by
    simpa using (Int.ModEq.refl (1 : ℤ)).sub he1
  set A : ℤ → Finset ι := fun x => Finset.univ.filter (fun i => x ≡ a i [ZMOD gM i]) with hAdef
  set sel : Finset ι → ℤ := fun s =>
    if h : s.Nonempty then a (Classical.choose (s.exists_min_image gq h)) else 0 with hseldef
  set ψ : ℕ → ℕ := fun x => (((x : ℤ) + e' * sel (A x)) % (L : ℤ)).toNat with hψdef
  have hψ : ∀ x : ℕ, x < L → ((ψ x : ℕ) : ℤ) = ((x : ℤ) + e' * sel (A x)) % (L : ℤ) := by
    intro x hx
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  unfold coverCount
  refine Finset.card_le_card_of_injOn ψ ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    have hxL := hx.1
    have hxψ := hψ x hxL
    refine ⟨?_, ?_⟩
    · have := Int.emod_lt_of_pos ((x : ℤ) + e' * sel (A x)) (by omega : (0 : ℤ) < L)
      omega
    obtain ⟨i, hi⟩ := hx.2
    rw [hsplit] at hi
    have hx0 : (x : ℤ) ≡ 0 [ZMOD gq i] := by
      have : a i * e ≡ 0 [ZMOD gq i] := by
        simpa using (he0'.of_dvd (Int.natCast_dvd_natCast.2 (hgq i))).mul_left (a i)
      exact hi.1.trans this
    have hiA : i ∈ A x := by
      simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and]
      have : a i * e ≡ a i [ZMOD gM i] := by
        simpa using (he1.of_dvd (Int.natCast_dvd_natCast.2 (hgM i))).mul_left (a i)
      exact hi.2.trans this
    have hne : (A x).Nonempty := ⟨i, hiA⟩
    obtain ⟨hjA, hjmin⟩ := Classical.choose_spec ((A x).exists_min_image gq hne)
    set j := Classical.choose ((A x).exists_min_image gq hne) with hjdef
    have hsel : sel (A x) = a j := by
      simp only [hseldef, hne, ↓reduceDIte, hjdef]
    have hjA' : (x : ℤ) ≡ a j [ZMOD gM j] := by
      simpa [hAdef] using hjA
    refine ⟨j, ?_⟩
    rw [hxψ, hsel, hsplit]
    constructor
    · have hgjL : ((gq j : ℕ) : ℤ) ∣ (L : ℤ) :=
        Int.natCast_dvd_natCast.2 ((hgq j).trans hqL)
      have h1 := (Int.mod_modEq ((x : ℤ) + e' * a j) L).of_dvd hgjL
      have h2 : (x : ℤ) ≡ 0 [ZMOD gq j] :=
        hx0.of_dvd (Int.natCast_dvd_natCast.2 (hchain j i (hjmin i hiA)))
      have h3 : e' * a j ≡ 1 * a j [ZMOD gq j] :=
        (he'1.of_dvd (Int.natCast_dvd_natCast.2 (hgq j))).mul_right _
      have := h1.trans (h2.add h3)
      simpa using this
    · have hgjL : ((gM j : ℕ) : ℤ) ∣ (L : ℤ) :=
        Int.natCast_dvd_natCast.2 ((hgM j).trans hML)
      have h1 := (Int.mod_modEq ((x : ℤ) + e' * a j) L).of_dvd hgjL
      have h3 : e' * a j ≡ 0 * a j [ZMOD gM j] :=
        (he'0.of_dvd (Int.natCast_dvd_natCast.2 (hgM j))).mul_right _
      have := h1.trans ((Int.ModEq.refl (x : ℤ)).add h3)
      simp only [zero_mul, add_zero] at this
      exact this.trans hjA'
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    have hc := congrArg (Nat.cast : ℕ → ℤ) hxy
    rw [hψ x hx.1, hψ y hy.1] at hc
    have hmodL : ((x : ℤ) + e' * sel (A x)) ≡ ((y : ℤ) + e' * sel (A y)) [ZMOD L] := hc
    have hmodM : (x : ℤ) ≡ y [ZMOD M] := by
      have h0 := hmodL.of_dvd (Int.natCast_dvd_natCast.2 hML)
      have h1 : (x : ℤ) + e' * sel (A x) ≡ x + 0 * sel (A x) [ZMOD M] :=
        (Int.ModEq.refl _).add (he'0.mul_right _)
      have h2 : (y : ℤ) + e' * sel (A y) ≡ y + 0 * sel (A y) [ZMOD M] :=
        (Int.ModEq.refl _).add (he'0.mul_right _)
      have := (h1.symm.trans h0).trans h2
      simpa using this
    have hA : A x = A y := by
      simp only [hAdef]
      refine Finset.filter_congr fun i _ => ?_
      have hm := hmodM.of_dvd (Int.natCast_dvd_natCast.2 (hgM i))
      exact ⟨fun h => hm.symm.trans h, fun h => hm.trans h⟩
    rw [hA] at hmodL
    have hxyL : (x : ℤ) ≡ y [ZMOD L] := Int.ModEq.add_right_cancel' _ hmodL
    exact Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.1 hxyL) hx.1 hy.1

omit [Fintype ι] in
lemma coverCount_of_dvd {L : ℕ} (n : ι → ℕ) (hn : ∀ i, n i ∣ L) (a : ι → ℤ)
    (ha : ∀ i, (L : ℤ) ∣ a i) : coverCount L n a = coverCount L n 0 := by
  unfold coverCount
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  refine exists_congr fun i => ?_
  have h1 : a i ≡ 0 [ZMOD n i] :=
    (Int.modEq_zero_iff_dvd.2 ((Int.natCast_dvd_natCast.2 (hn i)).trans (ha i)))
  exact ⟨fun h => h.trans h1, fun h => h.trans h1.symm⟩

/-- **Rogers' theorem** (counting form): over a common period `L` of the moduli, the number of
covered residues is minimized when all residues are `0`. -/
theorem coverCount_zero_le {L : ℕ} (hL : 0 < L) (n : ι → ℕ) (hn : ∀ i, n i ∣ L) (a : ι → ℤ) :
    coverCount L n 0 ≤ coverCount L n a := by
  suffices H : ∀ m d : ℕ, L - d ≤ m → d ∣ L → ∀ a : ι → ℤ, (∀ i, (d : ℤ) ∣ a i) →
      coverCount L n 0 ≤ coverCount L n a from
    H _ 1 le_rfl (one_dvd _) a (fun _ => by simp)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro d hdm hdL a ha
  by_cases hd : d = L
  · subst hd
    rw [coverCount_of_dvd n hn a ha]
  have hd0 : d ≠ 0 := by rintro rfl; simp at hdL; omega
  have hdlt : d < L := lt_of_le_of_ne (Nat.le_of_dvd hL hdL) hd
  obtain ⟨p, hpd⟩ : ∃ p, d.factorization p < L.factorization p := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hle := (Nat.factorization_le_iff_dvd hd0 hL.ne').2 hdL
    exact hd (Nat.eq_of_factorization_eq hd0 hL.ne' fun p => le_antisymm (hle p) (hcon p))
  have hp : p.Prime := by
    by_contra hnp
    simp [Nat.factorization_eq_zero_of_not_prime _ hnp] at hpd
  set q := p ^ L.factorization p with hqdef
  set M := L / q with hMdef
  have hLqM : L = q * M := (Nat.ordProj_mul_ordCompl_eq_self L p).symm
  have hcop : q.Coprime M := (Nat.coprime_ordCompl hp hL.ne').pow_left _
  have hqL : q ∣ L := Nat.ordProj_dvd L p
  -- Bézout idempotent
  have hic : IsCoprime (q : ℤ) (M : ℤ) := Int.isCoprime_iff_gcd_eq_one.2 (by simpa using hcop)
  obtain ⟨u, v, huv⟩ := hic
  set e : ℤ := u * q with he
  have he0 : (q : ℤ) ∣ e := ⟨u, by rw [he]; ring⟩
  have he1 : e ≡ 1 [ZMOD M] := by
    rw [Int.modEq_iff_dvd]; exact ⟨v, by rw [he]; linarith⟩
  have hstep := coverCount_compress hp rfl hcop hLqM n hn e he0 he1 a
  set d' := Nat.lcm d q
  have hd'L : d' ∣ L := Nat.lcm_dvd hdL hqL
  have hdd' : d ∣ d' := Nat.dvd_lcm_left d q
  have hd'ne : d' ≠ d := by
    intro h
    have : q ∣ d := h ▸ Nat.dvd_lcm_right d q
    have := (hp.pow_dvd_iff_le_factorization hd0).1 this
    omega
  have hd'lt : d < d' := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero (by
    intro h; rw [h] at hd'L; simp at hd'L; omega)) hdd') (Ne.symm hd'ne)
  have hd'le : d' ≤ L := Nat.le_of_dvd hL hd'L
  have ha' : ∀ i, (d' : ℤ) ∣ a i * e := by
    intro i
    have h1 : ((d * q : ℕ) : ℤ) ∣ a i * e := by
      push_cast; exact mul_dvd_mul (ha i) he0
    exact (Int.natCast_dvd_natCast.2 (Nat.lcm_dvd_mul d q)).trans h1
  exact (ih (L - d') (by omega) d' le_rfl hd'L _ ha').trans hstep

/-! ### Densities of periodic sets -/

omit [Fintype ι] in
lemma count_mul_period (s : Set ℕ) [DecidablePred (· ∈ s)] {L : ℕ} (hper : ∀ x, x + L ∈ s ↔ x ∈ s) :
    ∀ m : ℕ, Nat.count (· ∈ s) (m * L) = m * Nat.count (· ∈ s) L := by
  have hshift : ∀ m x, m * L + x ∈ s ↔ x ∈ s := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro x
      rw [show (m + 1) * L + x = (m * L + x) + L by ring, hper, ih]
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [add_mul, one_mul, Nat.count_add, ih, add_mul, one_mul]
    congr 1
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    congr 1
    exact Finset.filter_congr fun x _ => hshift m x

omit [Fintype ι] in
theorem hasNatDensity_of_periodic (s : Set ℕ) {L : ℕ} (hL : 0 < L)
    (hper : ∀ x, x + L ∈ s ↔ x ∈ s) :
    HasNatDensity s ((((Finset.range L).filter (· ∈ s)).card : ℝ) / L) := by
  have hshift : ∀ m x, m * L + x ∈ s ↔ x ∈ s := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro x
      rw [show (m + 1) * L + x = (m * L + x) + L by ring, hper, ih]
  set c : ℕ := Nat.count (· ∈ s) L with hc
  have hcL : ((Finset.range L).filter (· ∈ s)).card = c := by
    rw [hc, Nat.count_eq_card_filter_range]
  rw [hcL]
  unfold HasNatDensity
  have hbounds : ∀ N : ℕ, (N / L) * c ≤ ((Finset.range N).filter (· ∈ s)).card ∧
      ((Finset.range N).filter (· ∈ s)).card ≤ (N / L) * c + L := by
    intro N
    have hN : N = N / L * L + N % L := (Nat.div_add_mod' N L).symm
    have hr := Nat.count_le (fun k => N / L * L + k ∈ s) (n := N % L)
    have hmod := Nat.mod_lt N hL
    have key : Nat.count (· ∈ s) N =
        N / L * c + Nat.count (fun k => N / L * L + k ∈ s) (N % L) := by
      conv_lhs => rw [hN]
      rw [Nat.count_add, count_mul_period s hper]
    rw [← Nat.count_eq_card_filter_range, key]
    constructor <;> omega
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hc0 : (0 : ℝ) ≤ c := by positivity
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun N : ℕ => (c : ℝ) / L - c / N)
    (h := fun N : ℕ => (c : ℝ) / L + L / N)
  · simpa using (tendsto_const_nhds (x := (c : ℝ) / L)).sub
      (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
  · simpa using (tendsto_const_nhds (x := (c : ℝ) / L)).add
      (tendsto_const_div_atTop_nhds_zero_nat (L : ℝ))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨h1, -⟩ := hbounds N
    set X := ((Finset.range N).filter (· ∈ s)).card
    have hq : (N : ℝ) / L - 1 ≤ ((N / L : ℕ) : ℝ) := by
      have h := Nat.lt_div_mul_add (a := N) hL
      have : (N : ℝ) < (N / L : ℕ) * L + L := by exact_mod_cast h
      rw [div_sub_one hL'.ne', div_le_iff₀ hL']
      linarith
    have h1' : ((N / L : ℕ) : ℝ) * c ≤ X := by exact_mod_cast h1
    have h3 := mul_le_mul_of_nonneg_right hq hc0
    show (c : ℝ) / L - c / N ≤ X / N
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN']
    have : (c : ℝ) / L * N = N / L * c := by ring
    rw [this]
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨-, h2⟩ := hbounds N
    set X := ((Finset.range N).filter (· ∈ s)).card
    have hq : ((N / L : ℕ) : ℝ) ≤ (N : ℝ) / L := Nat.cast_div_le
    have h2' : (X : ℝ) ≤ ((N / L : ℕ) : ℝ) * c + L := by exact_mod_cast h2
    have h3 := mul_le_mul_of_nonneg_right hq hc0
    show (X : ℝ) / N ≤ c / L + L / N
    rw [div_le_iff₀ hN']
    have : ((c : ℝ) / L + L / N) * N = N / L * c + L := by field_simp
    rw [this]
    linarith

omit [Fintype ι] in
lemma card_multiples_of_dvd {m L : ℕ} (hmL : m ∣ L) (hL : 0 < L) :
    ((Finset.range L).filter (fun x => m ∣ x)).card = L / m := by
  have hm : 0 < m := Nat.pos_of_dvd_of_pos hmL hL
  have hper : ∀ x, x + m ∈ {x : ℕ | m ∣ x} ↔ x ∈ {x : ℕ | m ∣ x} := by
    intro x; simp [Nat.dvd_add_self_right]
  have h1 : Nat.count (· ∈ {x : ℕ | m ∣ x}) m = 1 := by
    rw [Nat.count_eq_card_filter_range, Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hd⟩; exact Nat.eq_zero_of_dvd_of_lt (show m ∣ x from hd) hx
    · rintro rfl; exact ⟨hm, show m ∣ 0 from dvd_zero _⟩
  have h2 := count_mul_period {x : ℕ | m ∣ x} hper (L / m)
  rw [Nat.div_mul_cancel hmL] at h2
  have h3 : Nat.count (· ∈ {x : ℕ | m ∣ x}) L = L / m := by
    rw [h2, h1, mul_one]
  rw [Nat.count_eq_card_filter_range] at h3
  simpa using h3

omit [Fintype ι] in
/-- Shifting all residues by the same constant does not change the covered count. -/
lemma coverCount_shift_le {L : ℕ} (hL : 0 < L) (n : ι → ℕ) (hn : ∀ i, n i ∣ L) (a : ι → ℤ)
    (c : ℤ) : coverCount L n (fun i => a i + c) ≤ coverCount L n a := by
  unfold coverCount
  have hpos : (0 : ℤ) < L := by exact_mod_cast hL
  refine Finset.card_le_card_of_injOn (fun x : ℕ => (((x : ℤ) - c) % L).toNat) ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    have h0 := Int.emod_nonneg ((x : ℤ) - c) hpos.ne'
    have h1 := Int.emod_lt_of_pos ((x : ℤ) - c) hpos
    refine ⟨by simp only; omega, ?_⟩
    obtain ⟨i, hi⟩ := hx.2
    refine ⟨i, ?_⟩
    rw [Int.toNat_of_nonneg h0]
    have h2 := (Int.mod_modEq ((x : ℤ) - c) L).of_dvd (Int.natCast_dvd_natCast.2 (hn i))
    have h3 := hi.sub (Int.ModEq.refl c)
    simp only [add_sub_cancel_right] at h3
    exact h2.trans h3
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    have hc := congrArg (Nat.cast : ℕ → ℤ) hxy
    simp only at hc
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne'),
      Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne')] at hc
    have h : ((x : ℤ) - c) ≡ ((y : ℤ) - c) [ZMOD L] := hc
    have hxy' : (x : ℤ) ≡ y [ZMOD L] := by simpa using h.add (Int.ModEq.refl c)
    exact Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.1 hxy') hx.1 hy.1

omit [Fintype ι] in
/-- All residues equal to a common value `c` gives the same count as all residues `0`. -/
lemma coverCount_const {L : ℕ} (hL : 0 < L) (n : ι → ℕ) (hn : ∀ i, n i ∣ L) (c : ℤ) :
    coverCount L n (fun _ => c) = coverCount L n 0 := by
  apply le_antisymm
  · calc coverCount L n (fun _ => c) = coverCount L n (fun i => (0 : ι → ℤ) i + c) := by
          congr 1; funext i; simp
      _ ≤ coverCount L n 0 := coverCount_shift_le hL n hn 0 c
  · calc coverCount L n 0 = coverCount L n (fun i => (fun _ => c) i + -c) := by
          congr 1; funext i; simp
      _ ≤ coverCount L n (fun _ => c) := coverCount_shift_le hL n hn (fun _ => c) (-c)

/-! ### Inclusion–exclusion for the all-zero system -/

theorem coverCount_zero_eq {L : ℕ} (hL : 0 < L) (n : ι → ℕ) (hn : ∀ i, n i ∣ L) :
    (coverCount L n 0 : ℤ) = ∑ t ∈ (Finset.univ : Finset ι).powerset.filter (·.Nonempty),
      (-1 : ℤ) ^ (t.card + 1) * ((L / t.lcm n : ℕ) : ℤ) := by
  set S : ι → Finset ℕ := fun i => (Finset.range L).filter (fun x => ((n i : ℕ) : ℤ) ∣ (x : ℤ))
  have hU : (Finset.range L).filter (fun x : ℕ => Covered n 0 x) = Finset.univ.biUnion S := by
    ext x
    simp [S, Covered, Int.modEq_zero_iff_dvd]
  unfold coverCount
  rw [hU, Finset.inclusion_exclusion_card_biUnion]
  conv_rhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 2
  have hinf : t.1.inf' (Finset.mem_filter.1 t.2).2 S =
      (Finset.range L).filter (fun x => t.1.lcm n ∣ x) := by
    ext x
    simp only [S, Finset.mem_inf', Finset.mem_filter, Finset.mem_range, Int.natCast_dvd_natCast,
      Finset.lcm_dvd_iff]
    constructor
    · intro h
      obtain ⟨i, hi⟩ := (Finset.mem_filter.1 t.2).2
      exact ⟨(h i hi).1, fun j hj => (h j hj).2⟩
    · rintro ⟨h1, h2⟩ j hj
      exact ⟨h1, h2 j hj⟩
  rw [hinf]
  exact card_multiples_of_dvd (Finset.lcm_mono (Finset.subset_univ _) |>.trans
    (Finset.lcm_dvd_iff.2 fun i _ => hn i)) hL

omit [Fintype ι] in
theorem hasNatDensity_covered {L : ℕ} (hL : 0 < L) (n : ι → ℕ) (hn : ∀ i, n i ∣ L)
    (a : ι → ℤ) :
    HasNatDensity {x : ℕ | Covered n a x} ((coverCount L n a : ℝ) / L) := by
  have hper : ∀ x : ℕ, x + L ∈ {x : ℕ | Covered n a x} ↔ x ∈ {x : ℕ | Covered n a x} := by
    intro x
    show Covered n a ((x + L : ℕ) : ℤ) ↔ Covered n a ((x : ℕ) : ℤ)
    simp only [Covered]
    refine exists_congr fun i => ?_
    have : ((x + L : ℕ) : ℤ) ≡ (x : ℤ) [ZMOD n i] := by
      rw [Int.modEq_iff_dvd]; push_cast; simpa using Int.natCast_dvd_natCast.2 (hn i)
    exact ⟨fun h => this.symm.trans h, fun h => this.trans h⟩
  have hcount : coverCount L n a =
      ((Finset.range L).filter (· ∈ {x : ℕ | Covered n a x})).card := by
    unfold coverCount
    exact congrArg Finset.card (Finset.filter_congr fun x _ => Iff.rfl)
  rw [hcount]
  exact hasNatDensity_of_periodic {x : ℕ | Covered n a x} hL hper

/-! ### Main theorem -/

/-- **Erdős Problem 278, second question (Rogers / Simpson).**
For positive moduli `n i`, every residue choice `a` yields a covered set with a natural density
`δ a`; the minimum over `a` is attained when all residues are equal (to `0`), and it equals
`∑_{∅ ≠ S ⊆ ι} (-1)^(|S|+1) / lcm (n i : i ∈ S)`. -/
theorem rogers_min_density (n : ι → ℕ) (hn : ∀ i, 0 < n i) :
    ∃ δ : (ι → ℤ) → ℝ,
      (∀ a, HasNatDensity {x : ℕ | Covered n a x} (δ a)) ∧
      (∀ a, δ 0 ≤ δ a) ∧
      (∀ c : ℤ, δ (fun _ => c) = δ 0) ∧
      δ 0 = ∑ t ∈ (Finset.univ : Finset ι).powerset.filter (·.Nonempty),
        (-1 : ℝ) ^ (t.card + 1) / ((t.lcm n : ℕ) : ℝ) := by
  set L : ℕ := (Finset.univ : Finset ι).lcm n with hLdef
  have hlcm0 : ∀ t : Finset ι, t.lcm n ≠ 0 := by
    intro t h
    obtain ⟨i, -, hi⟩ := Finset.lcm_eq_zero_iff.1 h
    exact (hn i).ne' hi
  have hL : 0 < L := Nat.pos_of_ne_zero (hlcm0 _)
  have hnL : ∀ i, n i ∣ L := fun i => Finset.dvd_lcm (Finset.mem_univ i)
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨fun a => (coverCount L n a : ℝ) / L, fun a => hasNatDensity_covered hL n hnL a,
    fun a => ?_, fun c => by simp only [coverCount_const hL n hnL c], ?_⟩
  · exact div_le_div_of_nonneg_right (by exact_mod_cast coverCount_zero_le hL n hnL a) hL'.le
  · have h := congrArg (Int.cast : ℤ → ℝ) (coverCount_zero_eq hL n hnL)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast] at h
    simp only
    rw [h, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    have htL : t.lcm n ∣ L := Finset.lcm_mono (Finset.subset_univ t)
    have ht0 : ((t.lcm n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hlcm0 t
    rw [Nat.cast_div htL ht0]
    field_simp

end CongruenceCovering
