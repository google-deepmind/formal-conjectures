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
# Erdős Problem 381

*References:*
- [erdosproblems.com/381](https://www.erdosproblems.com/381)
- [Er44] Erdős, P., *On highly composite numbers*. J. London Math. Soc. (1944), 130–133.
- [Ni71] Nicolas, Jean-Louis, *Répartition des nombres hautement composés de Ramanujan*.
  Canadian J. Math. (1971), 116–130.
- [Lean formalisation (plby)](https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos381.md)
-/

@[expose] public section

namespace Erdos381

def tau (n : ℕ) : ℕ := n.divisors.card

/-- A positive integer with more divisors than every smaller positive integer. -/
def HighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → tau m < tau n

def IsRecord (n : ℕ) : Prop :=
  0 < n ∧ ∀ m ∈ Finset.range n, 0 < m → tau m < tau n

instance (n : ℕ) : Decidable (IsRecord n) := by unfold IsRecord; infer_instance

@[category API, AMS 11]
theorem isRecord_iff (n : ℕ) : IsRecord n ↔ HighlyComposite n := by
  simp only [IsRecord, HighlyComposite, Finset.mem_range]
  constructor
  · rintro ⟨hn, h⟩
    exact ⟨hn, fun m hm hmn => h m hmn hm⟩
  · rintro ⟨hn, h⟩
    exact ⟨hn, fun m hmn hm => h m hm hmn⟩

def recordsUpTo (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter IsRecord

def count (N : ℕ) : ℕ := (recordsUpTo N).card

/-- The number of highly composite integers in $[1,x]$. -/
noncomputable def Q (x : ℝ) : ℕ := count ⌊x⌋₊

@[category API, AMS 11]
theorem mem_recordsUpTo {n N : ℕ} :
    n ∈ recordsUpTo N ↔ HighlyComposite n ∧ n ≤ N := by
  simp only [recordsUpTo, Finset.mem_filter, Finset.mem_Icc, isRecord_iff]
  constructor
  · rintro ⟨⟨_, hn⟩, hc⟩; exact ⟨hc, hn⟩
  · rintro ⟨hc, hn⟩; exact ⟨⟨hc.1, hn⟩, hc⟩

@[category API, AMS 11]
theorem mem_records_real {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    n ∈ recordsUpTo ⌊x⌋₊ ↔ HighlyComposite n ∧ (n : ℝ) ≤ x := by
  rw [mem_recordsUpTo, Nat.le_floor_iff hx]

@[category API, AMS 11]
theorem count_le (N : ℕ) : count N ≤ N := by
  unfold count recordsUpTo
  calc
    _ ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
    _ = N := by simp

@[category API, AMS 11]
theorem count_mono : Monotone count := by
  intro a b hab
  apply Finset.card_le_card
  intro n hn
  rw [mem_recordsUpTo] at hn ⊢
  exact ⟨hn.1, hn.2.trans hab⟩

@[category API, AMS 11]
theorem Q_mono : Monotone Q := fun _ _ h => count_mono (Nat.floor_mono h)

@[category API, AMS 11]
theorem not_highlyComposite_zero : ¬ HighlyComposite 0 := by simp [HighlyComposite]

@[category API, AMS 11]
theorem highlyComposite_one : HighlyComposite 1 := by
  refine ⟨by decide, ?_⟩
  intro m hm hlt
  omega

@[category API, AMS 11]
theorem count_zero : count 0 = 0 := by simp [count, recordsUpTo]

@[category API, AMS 11]
theorem Q_of_nonpos {x : ℝ} (hx : x ≤ 0) : Q x = 0 := by
  simp [Q, Nat.floor_eq_zero.mpr (by linarith : x < 1), count_zero]

@[category test, AMS 11]
theorem records_twelve : recordsUpTo 12 = {1, 2, 4, 6, 12} := by
  decide +kernel

@[category test, AMS 11]
theorem count_twelve : count 12 = 5 := by
  rw [count, records_twelve]
  decide

@[category API, AMS 11]
lemma tau_le (n : ℕ) : tau n ≤ n := Nat.card_divisors_le_self n

@[category API, AMS 11]
lemma tau_two_pow (k : ℕ) : tau (2 ^ k) = k + 1 := by
  simp [tau, Nat.divisors_prime_pow Nat.prime_two]

@[category API, AMS 11]
lemma tau_unbounded (N : ℕ) : ∃ n : ℕ, N < tau n := by
  refine ⟨2 ^ N, ?_⟩
  rw [tau_two_pow]
  omega

@[category API, AMS 11]
theorem highlyComposite_unbounded (N : ℕ) :
    ∃ n : ℕ, N < n ∧ HighlyComposite n := by
  obtain ⟨k, hk⟩ := tau_unbounded N
  let hex : ∃ n : ℕ, N < tau n := ⟨k, hk⟩
  let n := Nat.find hex
  have hn : N < tau n := Nat.find_spec hex
  have hN : N < n := lt_of_lt_of_le hn (tau_le n)
  refine ⟨n, hN, ?_⟩
  refine ⟨by omega, ?_⟩
  intro m _ hm
  have hm' : ¬ N < tau m := Nat.find_min hex hm
  omega

@[category API, AMS 11]
theorem highlyComposite_infinite : {n : ℕ | HighlyComposite n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hhc⟩ := highlyComposite_unbounded N
  exact ⟨n, hhc, hn⟩


@[category API, AMS 11]
theorem count_grows {N n : ℕ} (hn : N < n) (hc : HighlyComposite n) :
    count N < count n := by
  apply Finset.card_lt_card
  have hs : recordsUpTo N ⊆ recordsUpTo n := by
    intro m hm
    rw [mem_recordsUpTo] at hm ⊢
    exact ⟨hm.1, hm.2.trans (Nat.le_of_lt hn)⟩
  apply (Finset.ssubset_iff_of_subset hs).mpr
  refine ⟨n, mem_recordsUpTo.mpr ⟨hc, le_rfl⟩, ?_⟩
  intro h
  have hle := (mem_recordsUpTo.mp h).2
  omega

@[category API, AMS 11]
theorem count_unbounded (K : ℕ) : ∃ N : ℕ, K < count N := by
  induction K with
  | zero =>
    obtain ⟨n, hn, hc⟩ := highlyComposite_unbounded 0
    refine ⟨n, ?_⟩
    have hg := count_grows hn hc
    rw [count_zero] at hg
    exact hg
  | succ K ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨n, hn, hc⟩ := highlyComposite_unbounded N
    refine ⟨n, ?_⟩
    have hg := count_grows hn hc
    omega

@[category API, AMS 11]
theorem count_eventually_large (K : ℕ) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M → K < count M := by
  obtain ⟨N, hN⟩ := count_unbounded K
  exact ⟨N, fun M hM => lt_of_lt_of_le hN (count_mono hM)⟩

/-- The count $Q(x)$ eventually exceeds every natural number. -/
@[category API, AMS 11]
theorem Q_eventually_large (K : ℕ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → K < Q x := by
  obtain ⟨N, hN⟩ := count_unbounded K
  refine ⟨(N : ℝ), ?_⟩
  intro x hx
  exact lt_of_lt_of_le hN (count_mono (Nat.le_floor hx))

/-- Eventual lower bounds, with constants allowed to depend on the real exponent. -/
def lowerBound : Prop :=
  ∀ k : ℝ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ ∃ X : ℝ,
    ∀ x : ℝ, X ≤ x → c * (Real.log x) ^ k ≤ (Q x : ℝ)

/-- An eventual upper bound by a fixed power of the logarithm. -/
def upperBound : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ,
    ∀ x : ℝ, X ≤ x → (Q x : ℝ) ≤ C * (Real.log x) ^ B

@[category API, AMS 11]
theorem upper_not_lower : upperBound → ¬ lowerBound := by
  rintro ⟨B, hB, C, hC, X, hupper⟩ hlower
  obtain ⟨c, hc, Y, hlower⟩ := hlower (B + 1) (by linarith)
  let t : ℝ := max (Real.log (max X Y)) (C / c + 1)
  have hratio : 0 < C / c := div_pos hC hc
  have hbound : C / c + 1 ≤ t := le_max_right _ _
  have ht : 0 < t := by linarith
  have hxy : max X Y ≤ Real.exp t :=
    (Real.le_exp_log _).trans (Real.exp_le_exp.mpr (le_max_left _ _))
  have hx : X ≤ Real.exp t := (le_max_left _ _).trans hxy
  have hy : Y ≤ Real.exp t := (le_max_right _ _).trans hxy
  have hlo := hlower (Real.exp t) hy
  have hup := hupper (Real.exp t) hx
  rw [Real.log_exp, Real.rpow_add_one (ne_of_gt ht)] at hlo
  rw [Real.log_exp] at hup
  have hp : 0 < t ^ B := Real.rpow_pos_of_pos ht B
  have hprod : (c * t) * t ^ B ≤ C * t ^ B := by nlinarith [hlo.trans hup]
  have hct : c * t ≤ C := le_of_mul_le_mul_right hprod hp
  have hdivide : C / c < t := by linarith
  have hct' : C < t * c := (div_lt_iff₀ hc).mp hdivide
  nlinarith

/-- The proposed lower bounds for every real exponent $k \geq 1$. -/
def originalQuestion : Prop := lowerBound

/-- The logarithmic-power upper bound proved by Nicolas [Ni71]. -/
def nicolasUpperBound : Prop := upperBound

/-- Nicolas's upper bound implies the negative answer to the original question. -/
@[category API, AMS 11]
theorem refutation_of_nicolas_bound (h : nicolasUpperBound) : ¬ originalQuestion :=
  upper_not_lower h

/--
A number $n$ is highly composite if $\tau(m)<\tau(n)$ for all $m<n$, where $\tau(m)$ counts
the number of divisors of $m$. Let $Q(x)$ count the number of highly composite numbers in
$[1,x]$.

Is it true that $Q(x)\gg_k (\log x)^k$ for every $k\geq 1$?

The answer to this problem is no: Nicolas [Ni71] proved that $Q(x) \ll (\log x)^{O(1)}$.
-/
@[category research solved, AMS 11]
theorem erdos_381 : answer(False) ↔
    ∀ k : ℝ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ ∃ X : ℝ,
      ∀ x : ℝ, X ≤ x → c * (Real.log x) ^ k ≤ (Q x : ℝ) := by
  sorry

/-- Nicolas [Ni71] proved that $Q(x) \ll (\log x)^{O(1)}$. -/
@[category research solved, AMS 11]
theorem erdos_381.variants.nicolas_upper_bound : nicolasUpperBound := by
  sorry

end Erdos381
