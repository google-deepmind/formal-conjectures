/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 942

*Reference:* [erdosproblems.com/942](https://www.erdosproblems.com/942)
-/

@[expose] public section

open Nat Filter Topology

namespace Erdos942

/--
Let $h(n)$ count the number of powerful integers in $[n^2, (n + 1)^2)$.
-/
def erdos_942.h (n : ℕ) : ℕ := ((Finset.Ico (n ^ 2) ((n + 1) ^ 2)).filter Powerful).card

/--
Is there some constant $c > 0$ such that $h(n) < (\log n)^{c + o(1)}$ and, for infinitely many $n$,
$h(n) > (\log n)^{c - o(1)}$.
-/
@[category research open, question, AMS 11]
theorem erdos_942 : ∃ c > 0, ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    (∀ᶠ n in atTop, erdos_942.h n < (Real.log n) ^ (c + o n)) ∧
    {n | erdos_942.h n > (Real.log n) ^ (c - o n)}.Infinite := by
  sorry

/-- Squares are powerful. -/
lemma powerful_sq (m : ℕ) : Powerful (m ^ 2) := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hd : p ∣ m ^ 2 := Nat.dvd_of_mem_primeFactors hp
  have hm : p ∣ m := hpp.dvd_of_dvd_pow hd
  exact pow_dvd_pow_of_dvd hm 2

/-- `8 y²` is powerful. -/
lemma powerful_eight_mul_sq (y : ℕ) : Powerful (8 * y ^ 2) := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hd : p ∣ 8 * y ^ 2 := Nat.dvd_of_mem_primeFactors hp
  rcases (Nat.Prime.dvd_mul hpp).mp hd with h8 | hy
  · have h2 : p ∣ 2 ^ 3 := by simpa using h8
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h2)
    subst this
    exact Dvd.dvd.mul_right (by norm_num) _
  · exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (hpp.dvd_of_dvd_pow hy) 2) _

/-- `h n ≥ 1` for every `n` (`n²` itself is powerful). -/
lemma erdos_942.one_le_h (n : ℕ) : 1 ≤ erdos_942.h n := by
  unfold erdos_942.h
  apply Finset.card_pos.mpr
  refine ⟨n ^ 2, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨le_rfl, Nat.pow_lt_pow_left (Nat.lt_succ_self n) two_ne_zero⟩, powerful_sq n⟩

/-- The trivial upper bound `h n ≤ 2n + 1`. -/
lemma erdos_942.h_le (n : ℕ) : erdos_942.h n ≤ 2 * n + 1 := by
  unfold erdos_942.h
  calc _ ≤ (Finset.Ico (n ^ 2) ((n + 1) ^ 2)).card := Finset.card_filter_le _ _
    _ = 2 * n + 1 := by simp; ring_nf; omega

/-- Solutions of the Pell equation `x² - 8y² = 1`. -/
def pell : ℕ → ℕ × ℕ
  | 0 => (3, 1)
  | k + 1 => (3 * (pell k).1 + 8 * (pell k).2, (pell k).1 + 3 * (pell k).2)

lemma pell_eq (k : ℕ) : (pell k).1 ^ 2 = 8 * (pell k).2 ^ 2 + 1 := by
  induction k with
  | zero => simp [pell]
  | succ k ih => simp only [pell]; nlinarith [ih]

lemma pell_ge (k : ℕ) : k + 3 ≤ (pell k).1 := by
  induction k with
  | zero => simp [pell]
  | succ k ih => simp only [pell]; omega

/-- A Pell solution `x² = 8y² + 1` gives `h n ≥ 2` at `n = x - 1`. -/
lemma erdos_942.two_le_h_of_pell {x y : ℕ} (hx : 2 ≤ x) (h : x ^ 2 = 8 * y ^ 2 + 1) :
    2 ≤ erdos_942.h (x - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold erdos_942.h
  have hsub : ({n ^ 2, 8 * y ^ 2} : Finset ℕ) ⊆
      (Finset.Ico (n ^ 2) ((n + 1) ^ 2)).filter Powerful := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_filter, Finset.mem_Ico]
    rcases hz with rfl | rfl
    · exact ⟨⟨le_rfl, Nat.pow_lt_pow_left (Nat.lt_succ_self n) two_ne_zero⟩, powerful_sq n⟩
    · refine ⟨⟨?_, by omega⟩, powerful_eight_mul_sq y⟩
      nlinarith
  have hne : n ^ 2 ≠ 8 * y ^ 2 := by
    intro he; nlinarith
  calc 2 = ({n ^ 2, 8 * y ^ 2} : Finset ℕ).card := (Finset.card_pair hne).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- There are infinitely many `n` with `h n ≥ 2` (explicit construction from the Pell equation). -/
lemma erdos_942.two_le_h_infinite : {n | 2 ≤ erdos_942.h n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have h1 := erdos_942.two_le_h_of_pell (by have := pell_ge (B + 1); omega) (pell_eq (B + 1))
  have h2 := hB h1
  have := pell_ge (B + 1)
  omega

/-- A product of powerful numbers is powerful. -/
lemma powerful_mul {a b : ℕ} (ha : Powerful a) (hb : Powerful b) : Powerful (a * b) := by
  intro r hr
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hab : a * b ≠ 0 := (Nat.mem_primeFactors.mp hr).2.2
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
  rcases (Nat.Prime.dvd_mul hrp).mp (Nat.dvd_of_mem_primeFactors hr) with h | h
  · exact Dvd.dvd.mul_right (ha r (Nat.mem_primeFactors.mpr ⟨hrp, h, ha0⟩)) b
  · exact Dvd.dvd.mul_left (hb r (Nat.mem_primeFactors.mpr ⟨hrp, h, hb0⟩)) a

/-- A power with exponent at least 2 is powerful. -/
lemma powerful_pow (m j : ℕ) : Powerful (m ^ (j + 2)) := by
  intro r hr
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hm : r ∣ m := hrp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hr)
  exact (pow_dvd_pow_of_dvd hm 2).trans (pow_dvd_pow m (by omega))

/-- Transfers the real approximation `|y √d - q| < 1/2` to the natural interval `[(q-1)², (q+1)²)`. -/
lemma approx_to_nat {q d : ℕ} (hq : 0 < q) (hd : 0 < d) {y : ℤ}
    (h : |(y : ℝ) * Real.sqrt d - q| < 1 / 2) :
    ∃ m : ℕ, 0 < m ∧ (q - 1) ^ 2 ≤ m ^ 2 * d ∧ m ^ 2 * d < (q + 1) ^ 2 := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rw [abs_lt] at h
  have hy : 0 < y := by
    by_contra hc
    push Not at hc
    have : (y : ℝ) ≤ 0 := by exact_mod_cast hc
    nlinarith
  refine ⟨y.toNat, by omega, ?_, ?_⟩
  · have hc : ((y.toNat : ℕ) : ℝ) = y := by exact_mod_cast Int.toNat_of_nonneg hy.le
    have hr : (((y.toNat ^ 2 * d : ℕ)) : ℝ) = ((y : ℝ) * Real.sqrt d) ^ 2 := by
      push_cast; rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
    have hq' : (((q - 1 : ℕ)) : ℝ) = q - 1 := by rw [Nat.cast_sub hq]; simp
    have : (((q - 1) ^ 2 : ℕ) : ℝ) ≤ ((y.toNat ^ 2 * d : ℕ) : ℝ) := by
      rw [hr]; push_cast; rw [hq']; nlinarith
    exact_mod_cast this
  · have hc : ((y.toNat : ℕ) : ℝ) = y := by exact_mod_cast Int.toNat_of_nonneg hy.le
    have hr : (((y.toNat ^ 2 * d : ℕ)) : ℝ) = ((y : ℝ) * Real.sqrt d) ^ 2 := by
      push_cast; rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
    have : ((y.toNat ^ 2 * d : ℕ) : ℝ) < (((q + 1) ^ 2 : ℕ) : ℝ) := by
      rw [hr]; push_cast
      have h0 : 0 ≤ (y : ℝ) * Real.sqrt d := by nlinarith
      nlinarith
    exact_mod_cast this

/-- For distinct primes `p ≠ p'`, `m²p³ ≠ m'²p'³` (parity of the exponent of `p`). -/
lemma sq_mul_cube_ne {m m' p p' : ℕ} (hm : 0 < m) (hm' : 0 < m') (hp : p.Prime)
    (hp' : p'.Prime) (hne : p ≠ p') : m ^ 2 * p ^ 3 ≠ m' ^ 2 * p' ^ 3 := by
  intro h
  have h1 : (m ^ 2 * p ^ 3).factorization p = (m' ^ 2 * p' ^ 3).factorization p := by rw [h]
  rw [Nat.factorization_mul (by positivity) (pow_ne_zero 3 hp.ne_zero),
    Nat.factorization_mul (by positivity) (pow_ne_zero 3 hp'.ne_zero)] at h1
  simp only [Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    hp.factorization, hp'.factorization, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hne] at h1
  omega

/-- Simultaneous Dirichlet approximation (pigeonhole). -/
lemma dirichlet_simul (k M : ℕ) (hM : 0 < M) (θ : Fin k → ℝ) :
    ∃ q : ℕ, 0 < q ∧ ∀ i, ∃ y : ℤ, |(q : ℝ) * θ i - y| < 1 / M := by
  let f : ℕ → (Fin k → ℕ) := fun q i => ⌊(M : ℝ) * Int.fract ((q : ℝ) * θ i)⌋₊
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hmaps : ∀ q ∈ Finset.range (M ^ k + 1),
      f q ∈ Fintype.piFinset (fun _ : Fin k => Finset.range M) := by
    intro q _
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    apply (Nat.floor_lt (by positivity)).mpr
    have := Int.fract_lt_one ((q : ℝ) * θ i)
    nlinarith
  have hcard : (Fintype.piFinset (fun _ : Fin k => Finset.range M)).card <
      (Finset.range (M ^ k + 1)).card := by
    simp [Fintype.card_piFinset]
  have key : ∀ a b : ℕ, a < b → f a = f b →
      ∃ q : ℕ, 0 < q ∧ ∀ i, ∃ y : ℤ, |(q : ℝ) * θ i - y| < 1 / M := by
    intro a b hab hf
    refine ⟨b - a, by omega, fun i => ⟨⌊(b : ℝ) * θ i⌋ - ⌊(a : ℝ) * θ i⌋, ?_⟩⟩
    have hfi := congrFun hf i
    simp only [f] at hfi
    set u := (M : ℝ) * Int.fract ((a : ℝ) * θ i)
    set v := (M : ℝ) * Int.fract ((b : ℝ) * θ i)
    have hu0 : 0 ≤ u := by positivity
    have hv0 : 0 ≤ v := by positivity
    have h1 := Nat.floor_le hu0
    have h2 := Nat.lt_floor_add_one u
    have h3 := Nat.floor_le hv0
    have h4 := Nat.lt_floor_add_one v
    rw [hfi] at h1 h2
    have huv : |v - u| < 1 := by rw [abs_lt]; constructor <;> linarith
    have heq : ((b - a : ℕ) : ℝ) * θ i - ((⌊(b : ℝ) * θ i⌋ - ⌊(a : ℝ) * θ i⌋ : ℤ) : ℝ)
        = (v - u) / M := by
      simp only [u, v, Int.fract]
      rw [Nat.cast_sub hab.le]
      push_cast
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hMr]
    exact div_lt_div_of_pos_right huv hMr
  obtain ⟨a, _, b, _, hab, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h heq
  · exact key b a h heq.symm

/-- Key step: for every `k` there is `q ≥ 1` with `h (q-1) + h q ≥ k`
(simultaneous approximation placing every `m_i² p_i³`, for the first `k` primes `p_i`, near `q²`). -/
lemma erdos_942.exists_sum_h_ge (k : ℕ) :
    ∃ q : ℕ, 0 < q ∧ k ≤ erdos_942.h (q - 1) + erdos_942.h q := by
  let P : Fin k → ℕ := fun i => Nat.nth Nat.Prime i
  have hP : ∀ i, (P i).Prime := fun i => Nat.prime_nth_prime i
  let d : Fin k → ℕ := fun i => P i ^ 3
  have hd : ∀ i, 0 < d i := fun i => pow_pos (hP i).pos 3
  let S : ℕ := ∑ i, d i
  obtain ⟨q, hq, hy⟩ :=
    dirichlet_simul k (2 * (S + 1)) (by omega) (fun i => 1 / Real.sqrt (d i))
  have hm : ∀ i, ∃ m : ℕ, 0 < m ∧ (q - 1) ^ 2 ≤ m ^ 2 * d i ∧ m ^ 2 * d i < (q + 1) ^ 2 := by
    intro i
    obtain ⟨y, hyi⟩ := hy i
    apply approx_to_nat hq (hd i) (y := y)
    have hs : 0 < Real.sqrt (d i) := Real.sqrt_pos.mpr (by exact_mod_cast hd i)
    have hdS : (d i : ℝ) ≤ S := by
      exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    have hsS : Real.sqrt (d i) < S + 1 := by
      rw [Real.sqrt_lt' (by positivity)]; nlinarith
    have heq : (y : ℝ) * Real.sqrt (d i) - q =
        -(Real.sqrt (d i) * ((q : ℝ) * (1 / Real.sqrt (d i)) - y)) := by
      field_simp; ring
    rw [heq, abs_neg, abs_mul, abs_of_pos hs]
    calc _ < Real.sqrt (d i) * (1 / ((2 * (S + 1) : ℕ) : ℝ)) := by gcongr
      _ ≤ 1 / 2 := by
        push_cast
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  choose m hm0 hlo hhi using hm
  let g : Fin k → ℕ := fun i => m i ^ 2 * d i
  have hg : Function.Injective g := by
    intro i j hij
    by_contra hne
    exact sq_mul_cube_ne (hm0 i) (hm0 j) (hP i) (hP j)
      (fun h => hne (Fin.ext (Nat.nth_injective Nat.infinite_setOfPred_prime h))) hij
  have hsub : Finset.univ.image g ⊆ ((Finset.Ico ((q - 1) ^ 2) (q ^ 2)).filter Powerful) ∪
      ((Finset.Ico (q ^ 2) ((q + 1) ^ 2)).filter Powerful) := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    have hpow : Powerful (g i) := powerful_mul (powerful_pow (m i) 0) (powerful_pow (P i) 1)
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    by_cases hlt : g i < q ^ 2
    · exact Or.inl ⟨⟨hlo i, hlt⟩, hpow⟩
    · exact Or.inr ⟨⟨by omega, hhi i⟩, hpow⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin] at hc
  refine ⟨q, hq, hc.trans ((Finset.card_union_le _ _).trans ?_)⟩
  unfold erdos_942.h
  have : q - 1 + 1 = q := by omega
  rw [this]

/-- `h` is unbounded. -/
lemma erdos_942.exists_ge (k : ℕ) : ∃ n, k ≤ erdos_942.h n := by
  obtain ⟨q, _, hq⟩ := erdos_942.exists_sum_h_ge (2 * k)
  by_cases h : k ≤ erdos_942.h q
  · exact ⟨q, h⟩
  · exact ⟨q - 1, by omega⟩

/-- For each `k` there are infinitely many `n` with `h n ≥ k`. -/
lemma erdos_942.infinite_ge (k : ℕ) : {n | k ≤ erdos_942.h n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := erdos_942.exists_ge (k + 2 * B + 2)
  have h1 := erdos_942.h_le n
  have h2 : n ≤ B := hB (show k ≤ erdos_942.h n by omega)
  omega

/-- `limsup h = ∞` (the same statement as `erdos_942.variants.limsup`). -/
lemma erdos_942.limsup_eq_top :
    atTop.limsup (((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942.h)) = ⊤ := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  refine iInf_eq_top.mpr fun N => ?_
  refine ENat.eq_top_iff_forall_ge.mpr fun k => ?_
  obtain ⟨n, hn, hNn⟩ := Set.Infinite.exists_gt (erdos_942.infinite_ge k) N
  refine le_iSup₂_of_le n hNn.le ?_
  simp only [Function.comp_apply]
  exact_mod_cast hn

/--
It is not hard to prove that $\limsup h(n) = \infty$.
-/
@[category textbook, AMS 11]
theorem erdos_942.variants.limsup :
    atTop.limsup (((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942.h)) = ⊤ := by
  exact erdos_942.limsup_eq_top

/--
It is not hard to prove that the density $\delta_l$ of integers for which $h(n) = l$ exists
and satisfies $$\sum_l \delta_l = 1$$.
-/
@[category textbook, AMS 11]
theorem erdos_942.variants.density :
    ∃ δ : ℕ → ℝ, ∀ l, {n | erdos_942.h n = l}.HasDensity (δ l) ∧
    ∑' l, δ l = 1 := by
  sorry

end Erdos942
