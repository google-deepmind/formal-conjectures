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

import FormalConjecturesUtil

/-!
# Integrality and supercongruences of the factorial ratio $\frac{(6n)! n!}{(3n)! (2n)!^2}$

Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$

*References:*
- [A211417](https://oeis.org/A211417)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA211417


/--
Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$
-/
def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

open Nat Int Finset

def coprimeIndices (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun i => 1 ≤ i ∧ Nat.gcd i 30 = 1)

/--
The product term in the denominator of the general conjecture:
$$\prod_{i = 1..r, i \text{ coprime to } 30} (30n - i)$$
We define this in ℤ to handle the $n=0$ case where $30n-i$ in the product might be negative.
-/
def divisorProduct (n r : ℕ) : ℤ :=
  (coprimeIndices r).prod (fun i : ℕ => 30 * (n : ℤ) - (i : ℤ))

/-
### Auxiliary development for `general_divisibility`

Proof of Peter Bala's general `D(r)` conjecture: Landau step function, unit-class rigidity
(Lemma A), witness generalisation (Lemma B), prime-power stratification (Lemma C).

**Note on the statement of `general_divisibility` below.**  As currently written it is vacuous:
`D = 0` satisfies it, since every integer divides `0` (see `general_divisibility_is_vacuous`).
The mathematical content of Bala's conjecture needs `D ≠ 0`, so `general_divisibility_strong`
is also proved, with a positive witness; the literal statement is then discharged with that
same positive witness rather than with `0`.
-/

section BalaDr
/- ## Section 1: the Landau step function -/

/-- `f n d = ⌊30n/d⌋ + ⌊n/d⌋ - ⌊15n/d⌋ - ⌊10n/d⌋ - ⌊6n/d⌋`. -/
def f (n d : ℕ) : ℤ :=
  ((30 * n / d : ℕ) : ℤ) + ((n / d : ℕ) : ℤ) - ((15 * n / d : ℕ) : ℤ)
    - ((10 * n / d : ℕ) : ℤ) - ((6 * n / d : ℕ) : ℤ)

lemma helper_div (c m d : ℕ) : c * m / d = c * (m / d) + c * (m % d) / d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · simp [hd]
  · conv_lhs => rw [← Nat.div_add_mod m d]
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_add_div hd]

lemma div_two (m d : ℕ) : 15 * m / d = (30 * m / d) / 2 := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm d 2,
    ← Nat.mul_div_mul_left (15 * m) d (by norm_num : 0 < 2)]
  ring_nf

lemma div_three (m d : ℕ) : 10 * m / d = (30 * m / d) / 3 := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm d 3,
    ← Nat.mul_div_mul_left (10 * m) d (by norm_num : 0 < 3)]
  ring_nf

lemma div_five (m d : ℕ) : 6 * m / d = (30 * m / d) / 5 := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm d 5,
    ← Nat.mul_div_mul_left (6 * m) d (by norm_num : 0 < 5)]
  ring_nf

/-- Chebyshev nonnegativity of the step function. -/
lemma f_nonneg (n d : ℕ) : 0 ≤ f n d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · simp [f, hd]
  · have h30 := helper_div 30 n d
    have h15 := helper_div 15 n d
    have h10 := helper_div 10 n d
    have h6 := helper_div 6 n d
    have e15 := div_two (n % d) d
    have e10 := div_three (n % d) d
    have e6 := div_five (n % d) d
    have hu : 30 * (n % d) / d ≤ 29 := by
      have h1 : n % d < d := Nat.mod_lt _ hd
      exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by omega))
    unfold f
    omega

/-- **Lemma A (unit-class rigidity).**  `Δ_c = 1` for every residue `c ≤ 29` coprime to `30`. -/
lemma unit_step (c : ℕ) (h29 : c ≤ 29) (h2 : c % 2 ≠ 0) (h3 : c % 3 ≠ 0) (h5 : c % 5 ≠ 0) :
    c / 2 + c / 3 + c / 5 + 1 = c := by omega

lemma div30_two (q c : ℕ) : (30 * q + c) / 2 = 15 * q + c / 2 := by omega
lemma div30_three (q c : ℕ) : (30 * q + c) / 3 = 10 * q + c / 3 := by omega
lemma div30_five (q c : ℕ) : (30 * q + c) / 5 = 6 * q + c / 5 := by omega

/-- **Lemma B (witness generalisation).**  If `d ≥ 2`, `1 ≤ i < d`, `gcd(i,30) = 1`
and `d ∣ 30n - i`, then the step function takes the value `1`. -/
lemma f_eq_one (n d i : ℕ) (hd : 2 ≤ d) (hi1 : 1 ≤ i) (hid : i < d)
    (hgcd : Nat.gcd i 30 = 1) (hdvd : (d : ℤ) ∣ (30 * (n : ℤ) - (i : ℤ))) :
    f n d = 1 := by
  have hd0 : 0 < d := by omega
  -- Step 1: `30 * n % d = i`.
  have hmod : 30 * n % d = i := by
    have hmeq : (i : ℤ) % (d : ℤ) = (30 * (n : ℤ)) % (d : ℤ) :=
      (Int.modEq_iff_dvd.mpr hdvd)
    have hil : (i : ℤ) % (d : ℤ) = (i : ℤ) :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hid)
    have hcast : ((30 * n % d : ℕ) : ℤ) = (30 * (n : ℤ)) % (d : ℤ) := by
      push_cast; ring_nf
    have : ((30 * n % d : ℕ) : ℤ) = ((i : ℕ) : ℤ) := by rw [hcast, ← hmeq, hil]
    exact_mod_cast this
  -- Step 2: set up `C = 30n/d`, `q = n/d`, `s = n % d`.
  set q := n / d with hq
  set s := n % d with hs
  set C := 30 * n / d with hC
  have hns : d * q + s = n := Nat.div_add_mod n d
  have hCi : d * C + i = 30 * n := by
    have := Nat.div_add_mod (30 * n) d
    rw [← hmod]; exact this
  have hsd : s < d := Nat.mod_lt _ hd0
  -- Step 3: `C / 30 = q`, so `C = 30q + c` with `c = C % 30 ≤ 29`.
  have hCq : C / 30 = q := by
    have hlow : 30 * q ≤ C := by
      rw [hC]
      rw [Nat.le_div_iff_mul_le hd0]
      calc 30 * q * d = 30 * (d * q) := by ring
        _ ≤ 30 * n := by
            have : d * q ≤ n := by omega
            exact Nat.mul_le_mul_left 30 this
    have hhigh : C < 30 * q + 30 := by
      rw [hC, Nat.div_lt_iff_lt_mul hd0]
      have h1 : n < d * q + d := by omega
      calc 30 * n < 30 * (d * q + d) := by omega
        _ = (30 * q + 30) * d := by ring
    omega
  set c := C % 30 with hc
  have hCc : C = 30 * q + c := by omega
  have hc29 : c ≤ 29 := by omega
  -- Step 4: `d * c + i = 30 * s`.
  have hkey : d * c + i = 30 * s := by
    have h1 : d * C + i = 30 * (d * q + s) := by rw [hns]; exact hCi
    have h2 : d * (30 * q + c) + i = 30 * (d * q) + 30 * s := by
      rw [← hCc]; linarith [h1]
    nlinarith [h2]
  -- Step 5: `c` is coprime to 30.
  have key : ∀ t : ℕ, t ∣ 30 → t ∣ c → t ∣ i := by
    intro t ht htc
    have h1 : t ∣ 30 * s := ht.mul_right s
    have h2 : t ∣ d * c := htc.mul_left d
    rw [← hkey] at h1
    exact (Nat.dvd_add_right h2).mp h1
  have hnot : ∀ t : ℕ, 2 ≤ t → t ∣ 30 → ¬ (t ∣ c) := by
    intro t ht2 ht htc
    have hti := key t ht htc
    have : t ∣ Nat.gcd i 30 := Nat.dvd_gcd hti ht
    rw [hgcd] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h2 : c % 2 ≠ 0 := fun h => hnot 2 (by norm_num) (by norm_num) (Nat.dvd_of_mod_eq_zero h)
  have h3 : c % 3 ≠ 0 := fun h => hnot 3 (by norm_num) (by norm_num) (Nat.dvd_of_mod_eq_zero h)
  have h5 : c % 5 ≠ 0 := fun h => hnot 5 (by norm_num) (by norm_num) (Nat.dvd_of_mod_eq_zero h)
  -- Step 6: evaluate the step function.
  have e15 : 15 * n / d = C / 2 := by rw [hC]; exact div_two n d
  have e10 : 10 * n / d = C / 3 := by rw [hC]; exact div_three n d
  have e6 : 6 * n / d = C / 5 := by rw [hC]; exact div_five n d
  have hstep := unit_step c hc29 h2 h3 h5
  have hstepZ : ((c / 2 : ℕ) : ℤ) + ((c / 3 : ℕ) : ℤ) + ((c / 5 : ℕ) : ℤ) + 1 = (c : ℤ) := by
    exact_mod_cast hstep
  unfold f
  rw [e15, e10, e6, ← hC, ← hq, hCc, div30_two, div30_three, div30_five]
  push_cast
  linarith

/- ## Section 2: `p`-adic valuation of `a n` -/

/-- Numerator `(30n)! * n!`. -/
def num (n : ℕ) : ℕ := (30 * n).factorial * n.factorial

/-- Denominator `(15n)! * (10n)! * (6n)!`. -/
def den (n : ℕ) : ℕ := (15 * n).factorial * (10 * n).factorial * (6 * n).factorial

lemma num_ne_zero (n : ℕ) : num n ≠ 0 := by
  unfold num; positivity

lemma den_ne_zero (n : ℕ) : den n ≠ 0 := by
  unfold den; positivity

/-- Legendre's formula gives the difference of valuations as a sum of step values. -/
lemma legendre (p n b : ℕ) (hp : p.Prime) (hb : 30 * n < b) :
    (padicValNat p (num n) : ℤ) - (padicValNat p (den n) : ℤ)
      = ∑ k ∈ Finset.Ico 1 b, f n (p ^ k) := by
  haveI := Fact.mk hp
  have hlog : ∀ m : ℕ, m ≤ 30 * n → Nat.log p m < b := fun m hm =>
    lt_of_le_of_lt (le_trans (Nat.log_le_self p m) hm) hb
  have hnum : padicValNat p (num n)
      = padicValNat p ((30 * n).factorial) + padicValNat p (n.factorial) :=
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hden : padicValNat p (den n)
      = padicValNat p ((15 * n).factorial) + padicValNat p ((10 * n).factorial)
        + padicValNat p ((6 * n).factorial) := by
    unfold den
    rw [padicValNat.mul (by positivity) (Nat.factorial_ne_zero _),
      padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  have E30 := padicValNat_factorial (p := p) (n := 30 * n) (b := b) (hlog _ (le_refl _))
  have E1 := padicValNat_factorial (p := p) (n := n) (b := b) (hlog _ (by omega))
  have E15 := padicValNat_factorial (p := p) (n := 15 * n) (b := b) (hlog _ (by omega))
  have E10 := padicValNat_factorial (p := p) (n := 10 * n) (b := b) (hlog _ (by omega))
  have E6 := padicValNat_factorial (p := p) (n := 6 * n) (b := b) (hlog _ (by omega))
  rw [hnum, hden, E30, E1, E15, E10, E6]
  simp only [f, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  push_cast
  ring

lemma dvd_of_padicVal {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ p : ℕ, p.Prime → padicValNat p x ≤ padicValNat p y) : x ∣ y := by
  rw [← Nat.factorization_le_iff_dvd hx hy, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]; exact h p hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma den_dvd_num (n : ℕ) : den n ∣ num n := by
  refine dvd_of_padicVal (den_ne_zero n) (num_ne_zero n) (fun p hp => ?_)
  have hL := legendre p n (30 * n + 1) hp (by omega)
  have hpos : (0 : ℤ) ≤ ∑ k ∈ Finset.Ico 1 (30 * n + 1), f n (p ^ k) :=
    Finset.sum_nonneg (fun k _ => f_nonneg n (p ^ k))
  omega

lemma a_eq (n : ℕ) : a n = num n / den n := rfl

lemma a_mul (n : ℕ) : a n * den n = num n := by
  rw [a_eq]; exact Nat.div_mul_cancel (den_dvd_num n)

lemma a_ne_zero (n : ℕ) : a n ≠ 0 := by
  intro h
  have := a_mul n
  rw [h, zero_mul] at this
  exact num_ne_zero n this.symm

/-- The `p`-adic valuation of `a n` as a sum of step values. -/
lemma padicValNat_a (p n b : ℕ) (hp : p.Prime) (hb : 30 * n < b) :
    (padicValNat p (a n) : ℤ) = ∑ k ∈ Finset.Ico 1 b, f n (p ^ k) := by
  haveI := Fact.mk hp
  have h1 : padicValNat p (num n) = padicValNat p (a n) + padicValNat p (den n) := by
    rw [← a_mul n, padicValNat.mul (a_ne_zero n) (den_ne_zero n)]
  have h2 := legendre p n b hp hb
  omega

/- ## Section 3: counting divisibilities -/

lemma natAbs_dvd_iff (d : ℕ) (x : ℤ) : d ∣ x.natAbs ↔ (d : ℤ) ∣ x := by
  rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]

lemma natAbs_prod (s : Finset ℕ) (g : ℕ → ℤ) :
    (∏ i ∈ s, g i).natAbs = ∏ i ∈ s, (g i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Int.natAbs_mul, ih]

lemma padicValNat_prod (p : ℕ) [Fact p.Prime] (s : Finset ℕ) (g : ℕ → ℕ)
    (h : ∀ i ∈ s, g i ≠ 0) : padicValNat p (∏ i ∈ s, g i) = ∑ i ∈ s, padicValNat p (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      have hx0 : g x ≠ 0 := h x (Finset.mem_insert_self x s)
      have hs0 : ∀ i ∈ s, g i ≠ 0 := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hprod : (∏ i ∈ s, g i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs0
      rw [Finset.prod_insert hx, Finset.sum_insert hx, padicValNat.mul hx0 hprod, ih hs0]

/-- Counting the powers of `p` dividing `m`. -/
lemma count_pow_dvd (p m b : ℕ) [Fact p.Prime] (hm : m ≠ 0) (hb : padicValNat p m < b) :
    ∑ k ∈ Finset.Ico 1 b, (if p ^ k ∣ m then (1 : ℤ) else 0) = (padicValNat p m : ℤ) := by
  classical
  have hcongr : ∀ k ∈ Finset.Ico 1 b,
      (if p ^ k ∣ m then (1 : ℤ) else 0) = (if k ≤ padicValNat p m then (1 : ℤ) else 0) := by
    intro k _
    simp only [padicValNat_dvd_iff_le hm]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_boole]
  have hfilter : {k ∈ Finset.Ico 1 b | k ≤ padicValNat p m}
      = Finset.Ico 1 (padicValNat p m + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [hfilter, Nat.card_Ico]
  simp

lemma coprimeIndices_card_le (r : ℕ) : (coprimeIndices r).card ≤ r := by
  have hsub : coprimeIndices r ⊆ Finset.Ico 1 (r + 1) := by
    intro i hi
    simp only [coprimeIndices, Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_Ico]
    omega
  calc (coprimeIndices r).card ≤ (Finset.Ico 1 (r + 1)).card := Finset.card_le_card hsub
    _ = r := by simp

lemma coprimeIndices_mem {r i : ℕ} (hi : i ∈ coprimeIndices r) :
    1 ≤ i ∧ i ≤ r ∧ Nat.gcd i 30 = 1 := by
  simp only [coprimeIndices, Finset.mem_filter, Finset.mem_range] at hi
  exact ⟨hi.2.1, by omega, hi.2.2⟩

lemma term_ne_zero {r i : ℕ} (n : ℕ) (hi : i ∈ coprimeIndices r) :
    (30 * (n : ℤ) - (i : ℤ)) ≠ 0 := by
  obtain ⟨hi1, _, hgcd⟩ := coprimeIndices_mem hi
  intro h
  have h30 : (30 : ℤ) * (n : ℤ) = (i : ℤ) := by linarith
  have h30' : 30 * n = i := by exact_mod_cast h30
  have : (30 : ℕ) ∣ i := ⟨n, h30'.symm⟩
  rw [Nat.gcd_eq_right this] at hgcd
  omega

lemma lt_two_pow' (k : ℕ) : k < 2 ^ k := Nat.lt_two_pow_self

/-- The uniform per-layer bound.  This is Lemma C of the paper. -/
lemma per_k_bound (n r p k : ℕ) (_hp : p.Prime) (hr : 1 ≤ r) (_hk : 1 ≤ k) :
    ∑ i ∈ coprimeIndices r, (if p ^ k ∣ (30 * (n : ℤ) - (i : ℤ)).natAbs then (1 : ℤ) else 0)
      ≤ (if p ^ k ≤ r then (r : ℤ) else 0) + f n (p ^ k) := by
  classical
  by_cases hle : p ^ k ≤ r
  · rw [if_pos hle]
    have h1 : ∑ i ∈ coprimeIndices r,
        (if p ^ k ∣ (30 * (n : ℤ) - (i : ℤ)).natAbs then (1 : ℤ) else 0)
        ≤ ∑ _i ∈ coprimeIndices r, (1 : ℤ) :=
      Finset.sum_le_sum (fun i _ => by split <;> norm_num)
    have h2 : ((coprimeIndices r).card : ℤ) ≤ (r : ℤ) := by
      exact_mod_cast coprimeIndices_card_le r
    have h3 := f_nonneg n (p ^ k)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    linarith
  · rw [if_neg hle, zero_add]
    push_neg at hle
    have hpk2 : 2 ≤ p ^ k := by omega
    by_cases hex : ∃ i ∈ coprimeIndices r, p ^ k ∣ (30 * (n : ℤ) - (i : ℤ)).natAbs
    · obtain ⟨i0, hi0mem, hi0div⟩ := hex
      obtain ⟨hi01, hi0r, hi0gcd⟩ := coprimeIndices_mem hi0mem
      have hi0dvdZ : ((p ^ k : ℕ) : ℤ) ∣ (30 * (n : ℤ) - (i0 : ℤ)) :=
        (natAbs_dvd_iff _ _).mp hi0div
      have hone : ∀ i ∈ coprimeIndices r,
          (if p ^ k ∣ (30 * (n : ℤ) - (i : ℤ)).natAbs then (1 : ℤ) else 0)
            = (if i = i0 then (1 : ℤ) else 0) := by
        intro i hi
        obtain ⟨hi1, hir, _⟩ := coprimeIndices_mem hi
        by_cases hdi : p ^ k ∣ (30 * (n : ℤ) - (i : ℤ)).natAbs
        · have hdiZ : ((p ^ k : ℕ) : ℤ) ∣ (30 * (n : ℤ) - (i : ℤ)) :=
            (natAbs_dvd_iff _ _).mp hdi
          have hsub : ((p ^ k : ℕ) : ℤ) ∣ ((i0 : ℤ) - (i : ℤ)) := by
            have := dvd_sub hdiZ hi0dvdZ
            simpa using this
          have hlt : |((i0 : ℤ) - (i : ℤ))| < ((p ^ k : ℕ) : ℤ) := by
            rw [abs_lt]
            constructor
            · have : (i : ℤ) ≤ (r : ℤ) := by exact_mod_cast hir
              have h2 : (1 : ℤ) ≤ (i0 : ℤ) := by exact_mod_cast hi01
              have h3 : (r : ℤ) < ((p ^ k : ℕ) : ℤ) := by exact_mod_cast hle
              linarith
            · have : (i0 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hi0r
              have h2 : (1 : ℤ) ≤ (i : ℤ) := by exact_mod_cast hi1
              have h3 : (r : ℤ) < ((p ^ k : ℕ) : ℤ) := by exact_mod_cast hle
              linarith
          have := Int.eq_zero_of_abs_lt_dvd hsub hlt
          have hii : (i0 : ℤ) = (i : ℤ) := by linarith
          have : i = i0 := by exact_mod_cast hii.symm
          rw [if_pos hdi, if_pos this]
        · have hne : i ≠ i0 := by
            intro h; rw [h] at hdi; exact hdi hi0div
          rw [if_neg hdi, if_neg hne]
      rw [Finset.sum_congr rfl hone, Finset.sum_ite_eq' (coprimeIndices r) i0 (fun _ => (1 : ℤ)),
        if_pos hi0mem]
      have : f n (p ^ k) = 1 := by
        refine f_eq_one n (p ^ k) i0 hpk2 hi01 (by omega) hi0gcd ?_
        exact_mod_cast hi0dvdZ
      rw [this]
    · push_neg at hex
      have : ∑ i ∈ coprimeIndices r,
          (if p ^ k ∣ (30 * (n : ℤ) - (i : ℤ)).natAbs then (1 : ℤ) else 0) = 0 := by
        refine Finset.sum_eq_zero (fun i hi => ?_)
        rw [if_neg (hex i hi)]
      rw [this]
      exact f_nonneg n (p ^ k)

/-- The low-layer budget is absorbed by `(r!)^(r*r)`. -/
lemma S_bound (r p b : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    ∑ k ∈ Finset.Ico 1 b, (if p ^ k ≤ r then (r : ℤ) else 0)
      ≤ (padicValNat p ((r.factorial) ^ (r * r)) : ℤ) := by
  classical
  haveI := Fact.mk hp
  by_cases hpr : p ≤ r
  · have hv : 1 ≤ padicValNat p (r.factorial) := by
      rw [← padicValNat_dvd_iff_le (Nat.factorial_ne_zero r)]
      simpa using Nat.dvd_factorial hp.pos hpr
    -- NB: on older Mathlib (Lean 4.27 / formal-conjectures) `padicValNat.pow` takes the
    -- side condition `r ! ≠ 0`; there this reads `padicValNat.pow _ (Nat.factorial_ne_zero r)`.
    have hval : padicValNat p ((r.factorial) ^ (r * r))
        = (r * r) * padicValNat p (r.factorial) := padicValNat.pow _ (Nat.factorial_ne_zero r)
    have hcard : ({k ∈ Finset.Ico 1 b | p ^ k ≤ r}).card ≤ r := by
      have hsub : {k ∈ Finset.Ico 1 b | p ^ k ≤ r} ⊆ Finset.Ico 1 (r + 1) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_Ico] at hk
        simp only [Finset.mem_Ico]
        have h1 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
        have h2 : k < 2 ^ k := lt_two_pow' k
        omega
      calc ({k ∈ Finset.Ico 1 b | p ^ k ≤ r}).card
          ≤ (Finset.Ico 1 (r + 1)).card := Finset.card_le_card hsub
        _ = r := by simp
    have hsum : ∑ k ∈ Finset.Ico 1 b, (if p ^ k ≤ r then (r : ℤ) else 0)
        = (({k ∈ Finset.Ico 1 b | p ^ k ≤ r}).card : ℤ) * (r : ℤ) := by
      rw [← Finset.sum_filter]
      simp [Finset.sum_const]
    rw [hsum, hval]
    have hc : (({k ∈ Finset.Ico 1 b | p ^ k ≤ r}).card : ℤ) ≤ (r : ℤ) := by exact_mod_cast hcard
    have hr0 : (0 : ℤ) ≤ (r : ℤ) := by positivity
    have hstep : (({k ∈ Finset.Ico 1 b | p ^ k ≤ r}).card : ℤ) * (r : ℤ) ≤ (r : ℤ) * (r : ℤ) :=
      mul_le_mul_of_nonneg_right hc hr0
    have hfin : ((r : ℤ) * (r : ℤ)) ≤ ((r * r : ℕ) : ℤ) * (padicValNat p (r.factorial) : ℤ) := by
      have h1 : ((r * r : ℕ) : ℤ) = (r : ℤ) * (r : ℤ) := by push_cast; ring
      have h2 : (1 : ℤ) ≤ (padicValNat p (r.factorial) : ℤ) := by exact_mod_cast hv
      nlinarith [mul_nonneg hr0 hr0]
    push_cast at hfin ⊢
    linarith
  · push_neg at hpr
    have : ∑ k ∈ Finset.Ico 1 b, (if p ^ k ≤ r then (r : ℤ) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      simp only [Finset.mem_Ico] at hk
      have h1 : p ≤ p ^ k := Nat.le_self_pow (by omega) p
      rw [if_neg (by omega)]
    rw [this]
    positivity

/- ## Section 4: main theorem -/

/-- The witness constant.  (Far from optimal; the paper's `D(r)` is much smaller.) -/
def Dwit (r : ℕ) : ℤ := ((r.factorial : ℤ)) ^ (r * r)

lemma Dwit_pos (r : ℕ) : 0 < Dwit r := by
  unfold Dwit
  exact pow_pos (by exact_mod_cast Nat.factorial_pos r) _

/-- **Main divisibility, with the explicit witness `Dwit r = (r!)^(r^2)`.** -/
theorem key_dvd (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    (divisorProduct n r) ∣ (Dwit r * (a n : ℤ)) := by
  classical
  rw [← Int.natAbs_dvd_natAbs]
  have hDnat : (Dwit r * (a n : ℤ)).natAbs = (r.factorial) ^ (r * r) * a n := by
    unfold Dwit
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_natCast]
  rw [hDnat, divisorProduct, natAbs_prod]
  -- Reduce to a valuation inequality.
  have hQ0 : (∏ i ∈ coprimeIndices r, (30 * (n : ℤ) - (i : ℤ)).natAbs) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    simpa using term_ne_zero n hi
  have hR0 : (r.factorial) ^ (r * r) * a n ≠ 0 := by
    have := a_ne_zero n
    have h2 : (r.factorial) ^ (r * r) ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero r)
    exact Nat.mul_ne_zero h2 this
  refine dvd_of_padicVal hQ0 hR0 (fun p hp => ?_)
  haveI := Fact.mk hp
  set b := 30 * n + r + 1 with hb
  -- Right-hand side valuation.
  have hRval : padicValNat p ((r.factorial) ^ (r * r) * a n)
      = padicValNat p ((r.factorial) ^ (r * r)) + padicValNat p (a n) :=
    padicValNat.mul (pow_ne_zero _ (Nat.factorial_ne_zero r)) (a_ne_zero n)
  -- Left-hand side: product over `i`.
  have hLval : padicValNat p (∏ i ∈ coprimeIndices r, (30 * (n : ℤ) - (i : ℤ)).natAbs)
      = ∑ i ∈ coprimeIndices r, padicValNat p ((30 * (n : ℤ) - (i : ℤ)).natAbs) := by
    refine padicValNat_prod p _ _ (fun i hi => ?_)
    simpa using term_ne_zero n hi
  -- Each factor is a count of layers.
  have hcount : ∀ i ∈ coprimeIndices r,
      (padicValNat p ((30 * (n : ℤ) - (i : ℤ)).natAbs) : ℤ)
        = ∑ k ∈ Finset.Ico 1 b, (if p ^ k ∣ (30 * (n : ℤ) - (i : ℤ)).natAbs then (1 : ℤ) else 0) := by
    intro i hi
    obtain ⟨hi1, hir, _⟩ := coprimeIndices_mem hi
    have hm0 : (30 * (n : ℤ) - (i : ℤ)).natAbs ≠ 0 := by simpa using term_ne_zero n hi
    have hmle : (30 * (n : ℤ) - (i : ℤ)).natAbs ≤ 30 * n + r := by
      have h1 : (i : ℤ) ≤ (r : ℤ) := by exact_mod_cast hir
      omega
    have hvb : padicValNat p ((30 * (n : ℤ) - (i : ℤ)).natAbs) < b := by
      have h1 : p ^ padicValNat p ((30 * (n : ℤ) - (i : ℤ)).natAbs)
          ∣ (30 * (n : ℤ) - (i : ℤ)).natAbs := pow_padicValNat_dvd
      have h2 : p ^ padicValNat p ((30 * (n : ℤ) - (i : ℤ)).natAbs)
          ≤ (30 * (n : ℤ) - (i : ℤ)).natAbs := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h1
      have h3 : padicValNat p ((30 * (n : ℤ) - (i : ℤ)).natAbs)
          < 2 ^ padicValNat p ((30 * (n : ℤ) - (i : ℤ)).natAbs) := lt_two_pow' _
      have h4 : 2 ^ padicValNat p ((30 * (n : ℤ) - (i : ℤ)).natAbs)
          ≤ p ^ padicValNat p ((30 * (n : ℤ) - (i : ℤ)).natAbs) :=
        Nat.pow_le_pow_left hp.two_le _
      omega
    exact (count_pow_dvd p _ b hm0 hvb).symm
  -- Assemble.
  have step1 : (padicValNat p (∏ i ∈ coprimeIndices r, (30 * (n : ℤ) - (i : ℤ)).natAbs) : ℤ)
      = ∑ k ∈ Finset.Ico 1 b, ∑ i ∈ coprimeIndices r,
          (if p ^ k ∣ (30 * (n : ℤ) - (i : ℤ)).natAbs then (1 : ℤ) else 0) := by
    rw [hLval, Nat.cast_sum, Finset.sum_congr rfl hcount, Finset.sum_comm]
  have step2 : ∑ k ∈ Finset.Ico 1 b, ∑ i ∈ coprimeIndices r,
        (if p ^ k ∣ (30 * (n : ℤ) - (i : ℤ)).natAbs then (1 : ℤ) else 0)
      ≤ ∑ k ∈ Finset.Ico 1 b, ((if p ^ k ≤ r then (r : ℤ) else 0) + f n (p ^ k)) := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    simp only [Finset.mem_Ico] at hk
    exact per_k_bound n r p k hp hr hk.1
  have step3 : ∑ k ∈ Finset.Ico 1 b, ((if p ^ k ≤ r then (r : ℤ) else 0) + f n (p ^ k))
      = (∑ k ∈ Finset.Ico 1 b, (if p ^ k ≤ r then (r : ℤ) else 0))
        + (padicValNat p (a n) : ℤ) := by
    rw [Finset.sum_add_distrib, padicValNat_a p n b hp (by omega)]
  have step4 := S_bound r p b hp hr
  rw [hRval]
  have : (padicValNat p (∏ i ∈ coprimeIndices r, (30 * (n : ℤ) - (i : ℤ)).natAbs) : ℤ)
      ≤ (padicValNat p ((r.factorial) ^ (r * r)) : ℤ) + (padicValNat p (a n) : ℤ) := by
    rw [step1]
    calc _ ≤ ∑ k ∈ Finset.Ico 1 b, ((if p ^ k ≤ r then (r : ℤ) else 0) + f n (p ^ k)) := step2
      _ = (∑ k ∈ Finset.Ico 1 b, (if p ^ k ≤ r then (r : ℤ) else 0))
            + (padicValNat p (a n) : ℤ) := step3
      _ ≤ (padicValNat p ((r.factorial) ^ (r * r)) : ℤ) + (padicValNat p (a n) : ℤ) := by
          linarith
  exact_mod_cast this

/-- The statement of `general_divisibility` as given is vacuous: `D = 0` proves it. -/
lemma general_divisibility_is_vacuous (r : ℕ) :
    ∃ D : ℤ, ∀ n : ℕ, (divisorProduct n r) ∣ (D * (a n : ℤ)) :=
  ⟨0, fun n => by simp⟩

/--
Conjecture: "More generally, for r >= 1, we conjecture that there exists a constant D(r) such
that D(r)*a(n)/Product_{i = 1..r, i coprime to 30} (30*n - i) is integral for all n."
- _Peter Bala_, Aug 28 2025

This is the non-vacuous form, asserting a *positive* `D`; the witness is `Dwit r = (r!)^(r^2)`.
-/
theorem general_divisibility_strong (r : ℕ) (hr : 1 ≤ r) :
    ∃ D : ℤ, 0 < D ∧ ∀ n : ℕ, (divisorProduct n r) ∣ (D * (a n : ℤ)) :=
  ⟨Dwit r, Dwit_pos r, key_dvd r hr⟩

lemma coprimeIndices_one : coprimeIndices 1 = {1} := by decide

lemma divisorProduct_one (n : ℕ) : divisorProduct n 1 = 30 * (n : ℤ) - 1 := by
  rw [divisorProduct, coprimeIndices_one, Finset.prod_singleton]
  norm_num

lemma Dwit_one : Dwit 1 = 1 := by norm_num [Dwit]

end BalaDr


@[category test, AMS 11]
lemma a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma a_1 : a 1 = 77636318760 := by rfl

@[category test, AMS 11]
lemma a_2 : a 2 = 53837289804317953893960 := by rfl

@[category test, AMS 11]
lemma a_3 : a 3 = 43880754270176401422739454033276880 := by rfl

@[category test, AMS 11]
lemma a_4 : a 4 = 38113558705192522309151157825210540422513019720 := by rfl


/--
It appears that $a(n)/(30n - 1)$ is integral for all $n$ (checked up to $n = 1000$). - _Peter Bala_, Aug 28 2025

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/211417.wip.lean#L243"]
theorem thirty_mul_sub_one_dvd_a (n : ℕ) : (30 * (n : ℤ) - 1) ∣ (a n : ℤ) := by
    have h := key_dvd 1 (le_refl 1) n
    rwa [divisorProduct_one, Dwit_one, one_mul] at h

/--
Conjecture: "7*a(n)/(2*n + 1) ... [is an] integer for all n (checked up to n = 1000)."
- _Peter Bala_, Aug 28 2025
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a211417/blob/cad1fb228b5b80573cab3eeb92c8be57fd73c506/lean/OeisA211417FC.lean#L866-L868"]
theorem seven_mul_a_dvd_two_mul_add_one (n : ℕ) :
    (2 * (n : ℤ) + 1) ∣ 7 * (a n : ℤ) := by
  sorry

/--
Conjecture: "a(n)/(3*n + 1) ... [is an] integer for all n (checked up to n = 1000)."
- _Peter Bala_, Aug 28 2025
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a211417/blob/cad1fb228b5b80573cab3eeb92c8be57fd73c506/lean/OeisA211417FC.lean#L1173-L1175"]
theorem a_dvd_three_mul_add_one (n : ℕ) :
    (3 * (n : ℤ) + 1) ∣ (a n : ℤ) := by
  sorry

/--
Conjecture: "a(n)/(5*n + 1) ... [is an] integer for all n (checked up to n = 1000)."
- _Peter Bala_, Aug 28 2025
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a211417/blob/cad1fb228b5b80573cab3eeb92c8be57fd73c506/lean/OeisA211417FC.lean#L1446-L1448"]
theorem a_dvd_five_mul_add_one (n : ℕ) :
    (5 * (n : ℤ) + 1) ∣ (a n : ℤ) := by
  sorry

/--
Conjecture: "42*a(n)/((2*n + 1)*(3*n + 1)*(5*n + 1)) [is an] integer for all n
(checked up to n = 1000)." - _Peter Bala_, Aug 28 2025
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a211417/blob/cad1fb228b5b80573cab3eeb92c8be57fd73c506/lean/OeisA211417FC.lean#L1514-L1524"]
theorem forty_two_mul_a_dvd_product (n : ℕ) :
    ((2 * (n : ℤ) + 1) * (3 * (n : ℤ) + 1) * (5 * (n : ℤ) + 1)) ∣
      42 * (a n : ℤ) := by
  sorry

/--
Conjecture: "More generally, for r >= 1, we conjecture that there exists a constant D(r) such that
D(r)*a(n)/Product_{i = 1..r, i coprime to 30} (30*n - i) is integral for all n."
- _Peter Bala_, Aug 28 2025

This generalizes `thirty_mul_sub_one_dvd_a` (the $r = 1$ case where $D(1) = 1$).
-/
@[category research solved, AMS 11]
theorem general_divisibility (r : ℕ) (hr : 1 ≤ r) :
    ∃ D : ℤ, ∀ n : ℕ, (divisorProduct n r) ∣ (D * (a n : ℤ)) :=
  ⟨Dwit r, key_dvd r hr⟩

/--
Supercongruence: "a(p^k) == a(p^(k-1)) ( mod p^(3*k) ) for any prime p >= 5 and any positive
integer k." - _Peter Bala_, Jan 24 2020

More generally, "the congruences a(n*p^k) == a(n*p^(k-1)) ( mod p^(3*k) ) may hold for any
prime p >= 5 and any positive integers n and k."
-/
@[category research open, AMS 11]
theorem supercongruence (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ)) := by
  sorry

end OeisA211417
