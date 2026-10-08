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

public import FormalConjecturesUtil

/-!
# Erdős Problem 380

*References:*
- [erdosproblems.com/380](https://www.erdosproblems.com/380)
- [Ta26c] T. Tao, *Products of consecutive integers with unusual anatomy*.
  [arXiv:2603.27990v3](https://arxiv.org/abs/2603.27990v3) (2026),
  Definitions 1.2 and 1.4, Theorem 1.7.
-/

@[expose] public section

open scoped BigOperators
open Filter

namespace Erdos380

def intervalProduct (u v : ℕ) : ℕ := ∏ m ∈ Finset.Icc u v, m

def BadNumber (n : ℕ) : Prop := 1 < n ∧ Nat.maxPrimeFac n ^ 2 ∣ n

def BadInterval (u v : ℕ) : Prop :=
  1 ≤ u ∧ u ≤ v ∧ BadNumber (intervalProduct u v)

def Covered (n : ℕ) : Prop :=
  ∃ u v : ℕ, BadInterval u v ∧ u ≤ n ∧ n ≤ v

noncomputable def coveredUpTo (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter Covered

noncomputable def singletonUpTo (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter BadNumber

noncomputable def B (x : ℝ) : ℕ := (coveredUpTo ⌊x⌋₊).card
noncomputable def S (x : ℝ) : ℕ := (singletonUpTo ⌊x⌋₊).card

/-- The counting functions for bad intervals and bad singletons are asymptotic. -/
def MainTarget : Prop :=
  Tendsto (fun x : ℝ => (B x : ℝ) / (S x : ℝ)) atTop (nhds 1)

/-- Powerful numbers include 1, unlike bad numbers. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ Nat.Powerful n

def VeryBadInterval (u v : ℕ) : Prop :=
  1 ≤ u ∧ u ≤ v ∧ Powerful (intervalProduct u v)

def VeryCovered (n : ℕ) : Prop :=
  ∃ u v : ℕ, VeryBadInterval u v ∧ u ≤ n ∧ n ≤ v


@[simp, category API, AMS 11]
theorem intervalProduct_singleton (n : ℕ) : intervalProduct n n = n := by
  simp [intervalProduct]

@[simp, category API, AMS 11]
theorem badInterval_singleton_iff (n : ℕ) : BadInterval n n ↔ BadNumber n := by
  simp only [BadInterval, intervalProduct_singleton, le_refl, true_and]
  exact ⟨fun h => h.2, fun h => ⟨by have := h.1; omega, h⟩⟩

@[category API, AMS 11]
theorem badNumber_covered {n : ℕ} (h : BadNumber n) : Covered n :=
  ⟨n, n, (badInterval_singleton_iff n).2 h, le_rfl, le_rfl⟩

@[category API, AMS 11]
theorem covered_positive {n : ℕ} (h : Covered n) : 0 < n := by
  obtain ⟨u, v, hu, hun, hnv⟩ := h
  have := hu.1
  omega

@[simp, category API, AMS 11]
theorem not_bad_zero : ¬ BadNumber 0 := by simp [BadNumber]
@[simp, category API, AMS 11]
theorem not_bad_one : ¬ BadNumber 1 := by simp [BadNumber]
@[simp, category API, AMS 11]
theorem not_covered_zero : ¬ Covered 0 := by
  intro h
  have := covered_positive h
  omega

@[category API, AMS 11]
theorem singletonUpTo_subset (N : ℕ) : singletonUpTo N ⊆ coveredUpTo N := by
  classical
  intro n hn
  simp only [singletonUpTo, coveredUpTo, Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, badNumber_covered hn.2⟩

@[category API, AMS 11]
theorem singleton_count_le (N : ℕ) : (singletonUpTo N).card ≤ (coveredUpTo N).card :=
  Finset.card_le_card (singletonUpTo_subset N)

@[category API, AMS 11]
theorem S_le_B (x : ℝ) : S x ≤ B x := singleton_count_le _

@[category API, AMS 11]
theorem powerful_bad_of_one_lt {n : ℕ} (hn : 1 < n) (h : Powerful n) :
    BadNumber n :=
  ⟨hn, h.2 _ (Nat.mem_primeFactors.mpr ⟨Nat.prime_maxPrimeFac_of_one_lt n hn,
    Nat.maxPrimeFac_dvd, by omega⟩)⟩

@[category API, AMS 11]
theorem powerful_veryCovered {n : ℕ} (h : Powerful n) : VeryCovered n := by
  exact ⟨n, n, ⟨h.1, le_rfl, by simpa using h⟩, le_rfl, le_rfl⟩

/-- The integer $1$ is powerful, but is not a bad singleton. -/
@[category API, AMS 11]
theorem powerful_one : Powerful 1 := by
  exact ⟨by omega, Nat.Full.one_right 2⟩

@[category API, AMS 11]
theorem bad_prime_square {p : ℕ} (hp : p.Prime) : BadNumber (p ^ 2) := by
  have heq : Nat.maxPrimeFac (p ^ 2) = p := by
    rw [Nat.maxPrimeFac_pow (by omega : (2 : ℕ) ≠ 0), hp.maxPrimeFac_eq_self]
  refine ⟨?_, by rw [heq]⟩
  have := hp.two_le
  nlinarith

@[category API, AMS 11]
theorem bad_four : BadNumber 4 := by
  simpa using bad_prime_square Nat.prime_two

@[category API, AMS 11]
theorem S_pos_of_four_le {x : ℝ} (hx : 4 ≤ x) : 0 < S x := by
  classical
  apply Finset.card_pos.mpr
  refine ⟨4, ?_⟩
  simp only [singletonUpTo, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, (Nat.le_floor_iff (by linarith : 0 ≤ x)).2 (by exact_mod_cast hx)⟩,
    bad_four⟩

@[category API, AMS 11]
theorem S_eventually_pos : ∀ᶠ x : ℝ in atTop, 0 < S x := by
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
  exact S_pos_of_four_le hx

/-- Integers in bad intervals that are not bad singletons, up to $N$. -/
noncomputable def excessUpTo (N : ℕ) : Finset ℕ := coveredUpTo N \ singletonUpTo N
noncomputable def E (x : ℝ) : ℕ := (excessUpTo ⌊x⌋₊).card

@[category API, AMS 11]
theorem covered_card_partition (N : ℕ) :
    (coveredUpTo N).card = (singletonUpTo N).card + (excessUpTo N).card := by
  have := Finset.card_sdiff_add_card_eq_card (singletonUpTo_subset N)
  dsimp [excessUpTo]
  omega

@[category API, AMS 11]
theorem B_eq_S_add_E (x : ℝ) : B x = S x + E x := covered_card_partition _

@[category API, AMS 11]
theorem ratio_identity {x : ℝ} (hx : 0 < S x) :
    (B x : ℝ) / (S x : ℝ) = 1 + (E x : ℝ) / (S x : ℝ) := by
  have hne : (S x : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  rw [B_eq_S_add_E, Nat.cast_add, add_div, div_self hne]

/-- Negligible relative excess implies the main asymptotic. -/
@[category API, AMS 11]
theorem mainTarget_of_excess_negligible
    (h : Tendsto (fun x : ℝ => (E x : ℝ) / (S x : ℝ)) atTop (nhds 0)) :
    MainTarget := by
  have hid : (fun x : ℝ => (B x : ℝ) / (S x : ℝ)) =ᶠ[atTop]
      (fun x : ℝ => 1 + (E x : ℝ) / (S x : ℝ)) := by
    filter_upwards [S_eventually_pos] with x hx
    exact ratio_identity hx
  have ht := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).add h
  simp only [add_zero] at ht
  exact ht.congr' hid.symm

/-- The interval $[24,25]$ is bad. -/
@[category API, AMS 11]
theorem badInterval_24_25 : BadInterval 24 25 := by
  have hi : Finset.Icc (24 : ℕ) 25 = {24, 25} := by decide
  have hmax : Nat.maxPrimeFac 600 = 5 := by decide +kernel
  norm_num [BadInterval, BadNumber, intervalProduct, hi, hmax]

@[category API, AMS 11]
theorem covered_24 : Covered 24 :=
  ⟨24, 25, badInterval_24_25, by omega, by omega⟩

@[category API, AMS 11]
theorem not_bad_24 : ¬ BadNumber 24 := by
  have hmax : Nat.maxPrimeFac 24 = 3 := by decide +kernel
  norm_num [BadNumber, hmax]

@[category API, AMS 11]
theorem covered_not_iff_bad : ¬ (∀ n : ℕ, Covered n ↔ BadNumber n) := by
  intro h
  exact not_bad_24 ((h 24).1 covered_24)


/-- Every odd prime generates a two-element bad interval. -/
@[category API, AMS 11]
theorem badInterval_prime_square_pair {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    BadInterval (p ^ 2 - 1) (p ^ 2) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hsq : 9 ≤ p ^ 2 := by nlinarith
  have hpmod : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hodd
  have hsucc : ¬ (p + 1).Prime := by
    intro hs
    have := hs.eq_two_or_odd
    omega
  have hbound : Nat.maxPrimeFac (p + 1) ≤ p := by
    have hle := Nat.maxPrimeFac_le (n := p + 1)
    have hne : Nat.maxPrimeFac (p + 1) ≠ p + 1 := by
      intro he
      obtain hsmall | hprime := Nat.maxPrimeFac_eq_self_iff.mp he
      · omega
      · exact hsucc hprime
    omega
  have hfactor : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have h1 : p - 1 + 1 = p := by omega
    have h2 : p ^ 2 - 1 + 1 = p ^ 2 := by omega
    nlinarith
  have hprev : Nat.maxPrimeFac (p ^ 2 - 1) ≤ p := by
    rw [hfactor, Nat.maxPrimeFac_mul (by omega) (by omega)]
    exact max_le (by have := Nat.maxPrimeFac_le (n := p - 1); omega) hbound
  have hpow : Nat.maxPrimeFac (p ^ 2) = p := by simp [hp.maxPrimeFac_eq_self]
  have hproduct : intervalProduct (p ^ 2 - 1) (p ^ 2) = (p ^ 2 - 1) * p ^ 2 := by
    have heq : p ^ 2 = (p ^ 2 - 1) + 1 := by omega
    unfold intervalProduct
    conv_lhs => rw [heq]
    rw [Finset.prod_Icc_succ_top (by omega)]
    simp
    omega
  have hmax : Nat.maxPrimeFac (intervalProduct (p ^ 2 - 1) (p ^ 2)) = p := by
    rw [hproduct, Nat.maxPrimeFac_mul (by omega) (by positivity), hpow]
    exact max_eq_right hprev
  refine ⟨by omega, by omega, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [hproduct]
    have : 8 ≤ p ^ 2 - 1 := by omega
    nlinarith
  · rw [hmax, hproduct]
    exact dvd_mul_left _ _

/-- Multiplication by a positive factor with no larger prime preserves badness. -/
@[category API, AMS 11]
theorem badNumber_mul_of_maxPrimeFac_le {a b : ℕ} (ha : BadNumber a)
    (hb : 0 < b) (hsmooth : Nat.maxPrimeFac b ≤ Nat.maxPrimeFac a) :
    BadNumber (a * b) := by
  refine ⟨?_, ?_⟩
  · nlinarith [ha.1]
  · rw [Nat.maxPrimeFac_mul (by have := ha.1; omega) (by omega),
      max_eq_left hsmooth]
    exact dvd_mul_of_dvd_left ha.2 b

/-- The predecessor of an odd prime square belongs to a bad interval. -/
@[category API, AMS 11]
theorem covered_prime_square_predecessor {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    Covered (p ^ 2 - 1) := by
  exact ⟨p ^ 2 - 1, p ^ 2, badInterval_prime_square_pair hp hodd, le_rfl,
    Nat.sub_le _ _⟩

/-- Covered integers are unbounded, because every prime square is bad. -/
@[category API, AMS 11]
theorem covered_unbounded : ¬ BddAbove {n : ℕ | Covered n} := by
  rintro ⟨N, hN⟩
  obtain ⟨p, hlarge, hp⟩ := Nat.exists_infinite_primes (N + 2)
  have hcov := badNumber_covered (bad_prime_square hp)
  have hle := hN hcov
  have := hp.two_le
  nlinarith

@[category API, AMS 11]
theorem covered_infinite : Set.Infinite {n : ℕ | Covered n} :=
  Set.infinite_of_not_bddAbove covered_unbounded


/-- Every square of an integer at least two is a bad singleton. -/
@[category API, AMS 11]
theorem bad_square {n : ℕ} (hn : 2 ≤ n) : BadNumber (n ^ 2) := by
  refine ⟨by nlinarith, ?_⟩
  rw [Nat.maxPrimeFac_pow (by omega : (2 : ℕ) ≠ 0)]
  exact pow_dvd_pow_of_dvd Nat.maxPrimeFac_dvd 2

/-- At least $n-1$ distinct bad singletons are counted below $n^2$. -/
@[category API, AMS 11]
theorem singleton_count_square_lower (n : ℕ) :
    n - 1 ≤ (singletonUpTo (n ^ 2)).card := by
  classical
  have hsubset : (Finset.Icc 2 n).image (fun m => m ^ 2) ⊆ singletonUpTo (n ^ 2) := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hm2, hmn⟩ := Finset.mem_Icc.mp hm
    simp only [singletonUpTo, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by nlinarith, by nlinarith⟩, bad_square hm2⟩
  have hinj : Function.Injective (fun m : ℕ => m ^ 2) := by
    intro a b hab
    nlinarith
  have hc := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injective _ hinj, Nat.card_Icc] at hc
  omega

/-- The number of bad singletons tends to infinity. -/
@[category API, AMS 11]
theorem S_unbounded (K : ℕ) : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → K ≤ S x := by
  refine ⟨((K + 1) ^ 2 : ℕ), ?_⟩
  intro x hx
  have hfloor : (K + 1) ^ 2 ≤ ⌊x⌋₊ := by
    apply (Nat.le_floor_iff (by have : (0 : ℝ) ≤ ((K + 1) ^ 2 : ℕ) := Nat.cast_nonneg _; linarith : 0 ≤ x)).2
    exact hx
  have hmono : singletonUpTo ((K + 1) ^ 2) ⊆ singletonUpTo ⌊x⌋₊ := by
    classical
    intro n hn
    simp only [singletonUpTo, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans hfloor⟩, hn.2⟩
  have hcount := Finset.card_le_card hmono
  have hgrowth := singleton_count_square_lower (K + 1)
  change K ≤ (singletonUpTo ⌊x⌋₊).card
  omega

/-- The exact main asymptotic is equivalent to negligible relative excess. -/
@[category API, AMS 11]
theorem mainTarget_iff_excess_negligible : MainTarget ↔
    Tendsto (fun x : ℝ => (E x : ℝ) / (S x : ℝ)) atTop (nhds 0) := by
  refine ⟨?_, mainTarget_of_excess_negligible⟩
  intro h
  have hid : (fun x : ℝ => (E x : ℝ) / (S x : ℝ)) =ᶠ[atTop]
      (fun x : ℝ => (B x : ℝ) / (S x : ℝ) - 1) := by
    filter_upwards [S_eventually_pos] with x hx
    have hi := ratio_identity hx
    linarith
  have ht := h.sub (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ)))
  simp only [sub_self] at ht
  exact ht.congr' hid.symm


/--
We call an interval $[u,v]$ 'bad' if the greatest prime factor of $\prod_{u\leq m\leq v}m$
occurs with an exponent greater than $1$. Let $B(x)$ count the number of $n\leq x$ which
are contained in at least one bad interval. Is it true that
$$B(x)\sim \#\{ n\leq x: P(n)^2\mid n\},$$
where $P(n)$ is the largest prime factor of $n$?

Tao [Ta26c] has proved this asymptotic.

Intervals are positive and nonempty. The integer $1$ is not bad because it has no prime factors.
The witness interval for a counted integer may extend beyond $x$.
-/
@[category research solved, AMS 11]
@[formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos380.lean#L63"]
theorem erdos_380 : answer(True) ↔ MainTarget := by
  sorry

end Erdos380
