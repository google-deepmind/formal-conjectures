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

/-!
# Erdős Problem #311

Source: <https://www.erdosproblems.com/forum/thread/311>, which refers to
[ErGr80, p. 40].

Let `δ(N)` be the smallest nonzero value of `|1 - ∑_{n ∈ A} 1/n|` as `A` ranges over the
subsets of `{1, …, N}`. Is it true that `δ(N) = e^{-(c + o(1)) N}` for some constant
`c ∈ (0, 1)`?

Status: **OPEN**. This file contains
* faithful definitions of `δ(N)` (`erdos311Delta`) and of the Erdős–Graham variant
  (`erdos311DeltaEG`);
* the statement of the open question as a `Prop` (`Erdos311Conjecture`), **without** a proof;
* proved known/elementary results: the trivial bound `δ(N) ≥ 1/[1,…,N]`,
  the bound `δ(N) < 1/N` for `N ≥ 3`, monotonicity of `δ`, and the equivalence
  `δ(N) = δ_EG(N)` for every `N` (asserted by V. Kovac in the forum comments).
-/

open Filter Topology Real

@[expose] public section

namespace Erdos311

/-- The set of **nonzero** values of `|1 - ∑_{n ∈ A} 1/n|` with `A ⊆ {1, …, N}`. -/
def values (N : ℕ) : Set ℝ :=
  {x | x ≠ 0 ∧ ∃ A ⊆ Finset.Icc 1 N, x = |1 - ∑ n ∈ A, (1 : ℝ) / n|}

/-- `δ(N)`: the minimum of `values N`. (The set is finite and nonempty—`A = ∅` gives the value
`1`—so the infimum is an attained minimum; see `delta_mem`.) -/
noncomputable def erdos311Delta (N : ℕ) : ℝ := sInf (values N)

/-- Values in the original formulation of [ErGr80]: `A ⊆ {1,…,N}` contains no
`S` with `∑_{n ∈ S} 1/n = 1` (in particular, taking `S = A`, the value is nonzero). -/
def valuesEG (N : ℕ) : Set ℝ :=
  {x | ∃ A ⊆ Finset.Icc 1 N, (∀ S ⊆ A, ∑ n ∈ S, (1 : ℝ) / n ≠ 1) ∧
    x = |1 - ∑ n ∈ A, (1 : ℝ) / n|}

/-- `δ(N)` in the original formulation of [ErGr80]. -/
noncomputable def erdos311DeltaEG (N : ℕ) : ℝ := sInf (valuesEG N)

/-- **Erdős #311 (open question).** There exists `c ∈ (0,1)` such that
`δ(N) = exp (-(c + o(1)) N)`, that is, there exists a function `ε : ℕ → ℝ` with `ε N → 0`
and `δ(N) = exp (-(c + ε N) N)` for every `N ≥ 1`. -/
def Erdos311Conjecture : Prop :=
  ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ N ≥ 1, erdos311Delta N = Real.exp (-(c + ε N) * N)

/-! ### Basic properties of `δ` -/

/-- Abbreviation: `|1 - ∑_{n∈A} 1/n|`. -/
noncomputable abbrev gap (A : Finset ℕ) : ℝ := |1 - ∑ n ∈ A, (1 : ℝ) / n|

lemma values_finite (N : ℕ) : (values N).Finite := by
  apply ((Finset.Icc 1 N).powerset.finite_toSet.image gap).subset
  rintro x ⟨-, A, hA, rfl⟩
  exact ⟨A, Finset.mem_coe.mpr (Finset.mem_powerset.mpr hA), rfl⟩

lemma one_mem_values (N : ℕ) : (1 : ℝ) ∈ values N :=
  ⟨one_ne_zero, ∅, Finset.empty_subset _, by simp⟩

lemma delta_mem (N : ℕ) : erdos311Delta N ∈ values N :=
  Set.Nonempty.csInf_mem ⟨1, one_mem_values N⟩ (values_finite N)

lemma delta_le {N : ℕ} {x : ℝ} (hx : x ∈ values N) : erdos311Delta N ≤ x :=
  csInf_le (values_finite N).bddBelow hx

lemma delta_le_gap {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (h : gap A ≠ 0) :
    erdos311Delta N ≤ gap A :=
  delta_le ⟨h, A, hA, rfl⟩

/-- `δ(N) > 0`. -/
theorem delta_pos (N : ℕ) : 0 < erdos311Delta N := by
  obtain ⟨h0, A, -, h⟩ := delta_mem N
  rw [h] at h0 ⊢
  exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)

/-- `δ` is nonincreasing. -/
theorem delta_antitone : Antitone erdos311Delta := by
  intro M N hMN
  obtain ⟨h0, A, hA, h⟩ := delta_mem M
  refine delta_le ⟨h0, A, hA.trans (Finset.Icc_subset_Icc le_rfl hMN), h⟩

lemma valuesEG_finite (N : ℕ) : (valuesEG N).Finite := by
  apply ((Finset.Icc 1 N).powerset.finite_toSet.image gap).subset
  rintro x ⟨A, hA, -, rfl⟩
  exact ⟨A, Finset.mem_coe.mpr (Finset.mem_powerset.mpr hA), rfl⟩

lemma one_mem_valuesEG (N : ℕ) : (1 : ℝ) ∈ valuesEG N := by
  refine ⟨∅, Finset.empty_subset _, ?_, by simp⟩
  intro S hS
  rw [Finset.subset_empty.mp hS]
  simp

lemma deltaEG_mem (N : ℕ) : erdos311DeltaEG N ∈ valuesEG N :=
  Set.Nonempty.csInf_mem ⟨1, one_mem_valuesEG N⟩ (valuesEG_finite N)

lemma deltaEG_le {N : ℕ} {x : ℝ} (hx : x ∈ valuesEG N) : erdos311DeltaEG N ≤ x :=
  csInf_le (valuesEG_finite N).bddBelow hx

/-! ### Reformulation of the conjecture -/

/-- The form `δ(N) = e^{-(c+o(1))N}` is equivalent to `-log δ(N) / N → c`. -/
theorem conjecture_iff_tendsto :
    Erdos311Conjecture ↔ ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun N : ℕ => -Real.log (erdos311Delta N) / N) atTop (𝓝 c) := by
  constructor
  · rintro ⟨c, hc, ε, hε, h⟩
    refine ⟨c, hc, ?_⟩
    have : Tendsto (fun N => c + ε N) atTop (𝓝 c) := by simpa using hε.const_add c
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [h N hN, Real.log_exp]
    field_simp
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun N => -Real.log (erdos311Delta N) / N - c, ?_, ?_⟩
    · simpa using h.sub_const c
    · intro N hN
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      have : -(c + (-Real.log (erdos311Delta N) / N - c)) * N = Real.log (erdos311Delta N) := by
        field_simp
        ring
      rw [this, Real.exp_log (delta_pos N)]

/-! ### The trivial bound `δ(N) ≥ 1/[1,…,N]` -/

/-- Trivial bound: `δ(N) ≥ 1 / [1, …, N]`, where `[1,…,N]` is the least common multiple. -/
theorem one_div_lcm_le_delta (N : ℕ) :
    1 / (((Finset.Icc 1 N).lcm id : ℕ) : ℝ) ≤ erdos311Delta N := by
  set L : ℕ := (Finset.Icc 1 N).lcm id with hL
  have hLpos : 0 < L := by
    rw [Nat.pos_iff_ne_zero, hL, Ne, Finset.lcm_eq_zero_iff]
    simp
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  obtain ⟨h0, A, hA, hx⟩ := delta_mem N
  rw [hx]
  -- `L * ∑_{n ∈ A} 1/n` is an integer.
  have hsum : (L : ℝ) * ∑ n ∈ A, (1 : ℝ) / n = ((∑ n ∈ A, L / n : ℕ) : ℝ) := by
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (hA hn)).1
    have hdvd : n ∣ L := Finset.dvd_lcm (f := id) (hA hn)
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [Nat.cast_div hdvd hnR]
    ring
  set M : ℕ := ∑ n ∈ A, L / n
  have key : (L : ℝ) * (1 - ∑ n ∈ A, (1 : ℝ) / n) = (((L : ℤ) - M : ℤ) : ℝ) := by
    rw [mul_sub, hsum]
    push_cast
    ring
  have hk : ((L : ℤ) - M : ℤ) ≠ 0 := by
    intro hk
    apply h0
    rw [hk, Int.cast_zero] at key
    have : 1 - ∑ n ∈ A, (1 : ℝ) / n = 0 := by
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h hLR.ne'
      · exact h
    rw [hx, this, abs_zero]
  have hk1 : (1 : ℝ) ≤ |(((L : ℤ) - M : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk
  rw [div_le_iff₀ hLR, ← key, abs_mul, abs_of_pos hLR] at *
  linarith [hk1]

/-! ### `δ(N) < 1/N` for `N ≥ 3` (Sylvester sequence) -/

/-- Sylvester sequence: `2, 3, 7, 43, 1807, …`. -/
def syl : ℕ → ℕ
  | 0 => 2
  | j + 1 => syl j * (syl j - 1) + 1

lemma two_le_syl (j : ℕ) : 2 ≤ syl j := by
  induction j with
  | zero => simp [syl]
  | succ j ih =>
    obtain ⟨t, ht⟩ : ∃ t, syl j = t + 2 := ⟨syl j - 2, by omega⟩
    simp only [syl, ht]
    rw [show t + 2 - 1 = t + 1 by omega]
    nlinarith

lemma syl_lt_succ (j : ℕ) : syl j < syl (j + 1) := by
  obtain ⟨t, ht⟩ : ∃ t, syl j = t + 2 := ⟨syl j - 2, by have := two_le_syl j; omega⟩
  simp only [syl, ht]
  rw [show t + 2 - 1 = t + 1 by omega]
  nlinarith

lemma syl_strictMono : StrictMono syl := strictMono_nat_of_lt_succ syl_lt_succ

/-- `∑_{i ≤ j} 1/s_i = 1 - 1/(s_{j+1} - 1)`. -/
lemma sum_inv_syl (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), (1 : ℝ) / syl i = 1 - 1 / ((syl (j + 1) : ℝ) - 1) := by
  induction j with
  | zero => norm_num [syl]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    have h2 := two_le_syl (j + 1)
    have hcast : ((syl (j + 1 + 1) : ℕ) : ℝ) - 1
        = (syl (j + 1) : ℝ) * ((syl (j + 1) : ℝ) - 1) := by
      rw [show syl (j + 1 + 1) = syl (j + 1) * (syl (j + 1) - 1) + 1 from rfl]
      push_cast [Nat.cast_sub (show 1 ≤ syl (j + 1) by omega)]
      ring
    rw [hcast]
    have hs : (2 : ℝ) ≤ syl (j + 1) := by exact_mod_cast h2
    have h1 : (syl (j + 1) : ℝ) - 1 ≠ 0 := by linarith
    have h0 : (syl (j + 1) : ℝ) ≠ 0 := by linarith
    field_simp
    ring

/-- For `N ≥ 3`, `δ(N) < 1/N`. -/
theorem delta_lt_inv {N : ℕ} (hN : 3 ≤ N) : erdos311Delta N < 1 / N := by
  have hex : ∃ k, N < syl k :=
    ⟨N + 1, lt_of_lt_of_le (Nat.lt_succ_self N) (syl_strictMono.id_le _)⟩
  obtain ⟨k, hk, hmin⟩ : ∃ k, N < syl k ∧ ∀ m < k, ¬ N < syl m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hk2 : 2 ≤ k := by
    by_contra hcon
    interval_cases k
    · simp [syl] at hk; omega
    · simp [syl] at hk; omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjN : syl j ≤ N := not_lt.mp (hmin j (Nat.lt_succ_self j))
  have hj3 : 3 ≤ syl j := by
    have : syl 1 ≤ syl j := syl_strictMono.monotone (by omega)
    simpa [syl] using this
  set B := (Finset.range (j + 1)).image syl with hB
  have hBsum : ∑ n ∈ B, (1 : ℝ) / n = 1 - 1 / ((syl (j + 1) : ℝ) - 1) := by
    rw [hB, Finset.sum_image (fun a _ b _ h => syl_strictMono.injective h), sum_inv_syl]
  have hBle : ∀ n ∈ B, n ≤ syl j := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    exact syl_strictMono.monotone (by simpa [Nat.lt_succ_iff] using hi)
  have hBsub : B ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hn
    refine Finset.mem_Icc.mpr ⟨by linarith [two_le_syl i], ?_⟩
    exact (hBle _ hn).trans hjN
  have hsucc : syl (j + 1) = syl j * (syl j - 1) + 1 := rfl
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  rcases Nat.lt_or_ge N (syl (j + 1) - 1) with hlt | hge
  · -- Case `N < s_{j+1} - 1`: `B` suffices.
    have hP : (N : ℝ) < (syl (j + 1) : ℝ) - 1 := by
      have : (N : ℝ) + 1 < syl (j + 1) := by exact_mod_cast (show N + 1 < syl (j + 1) by omega)
      linarith
    have hgap : gap B = 1 / ((syl (j + 1) : ℝ) - 1) := by
      rw [gap, hBsum, sub_sub_cancel, abs_of_pos (by apply div_pos one_pos; linarith)]
    have hne : gap B ≠ 0 := by
      rw [hgap]; apply ne_of_gt; apply div_pos one_pos; linarith
    calc erdos311Delta N ≤ gap B := delta_le_gap hBsub hne
      _ = _ := hgap
      _ < 1 / N := one_div_lt_one_div_of_lt (by linarith) hP
  · -- Case `N = s_{j+1} - 1`: add `N - 1`.
    have hNeq : N = syl (j + 1) - 1 := by omega
    have hNR' : (N : ℝ) = (syl (j + 1) : ℝ) - 1 := by
      rw [hNeq, Nat.cast_sub (by linarith [two_le_syl (j + 1)])]; simp
    have hbig : syl j < N - 1 := by
      rw [hNeq, hsucc]
      obtain ⟨t, ht⟩ : ∃ t, syl j = t + 3 := ⟨syl j - 3, by omega⟩
      rw [ht, show t + 3 - 1 = t + 2 by omega,
        show (t + 3) * (t + 2) + 1 - 1 - 1 = t * t + 5 * t + 5 by ring_nf; omega]
      nlinarith
    have hnot : N - 1 ∉ B := fun h => by have := hBle _ h; omega
    set B' := insert (N - 1) B
    have hB'sub : B' ⊆ Finset.Icc 1 N := by
      intro n hn
      rcases Finset.mem_insert.mp hn with rfl | hn
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · exact hBsub hn
    have hcast1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hgap : gap B' = 1 / ((N : ℝ) - 1) - 1 / N := by
      rw [gap, Finset.sum_insert hnot, hBsum, ← hNR', hcast1]
      have h1 : 1 / (N : ℝ) < 1 / ((N : ℝ) - 1) :=
        one_div_lt_one_div_of_lt (by linarith) (by linarith)
      rw [abs_of_neg (by linarith)]
      ring
    have hpos : 0 < gap B' := by
      rw [hgap]
      have : 1 / (N : ℝ) < 1 / ((N : ℝ) - 1) :=
        one_div_lt_one_div_of_lt (by linarith) (by linarith)
      linarith
    calc erdos311Delta N ≤ gap B' := delta_le_gap hB'sub hpos.ne'
      _ = 1 / ((N : ℝ) - 1) - 1 / N := hgap
      _ < 1 / N := by
        have h0 : (N : ℝ) - 1 ≠ 0 := by linarith
        have h0' : (N : ℝ) ≠ 0 := by linarith
        rw [div_sub_div _ _ h0 h0', div_lt_div_iff₀ (by nlinarith) (by linarith)]
        nlinarith

/-! ### Equivalence with the [ErGr80] formulation -/

/-- The additional condition in [ErGr80] does not change `δ(N)` for any `N`. -/
theorem delta_eq_deltaEG (N : ℕ) : erdos311Delta N = erdos311DeltaEG N := by
  apply le_antisymm
  · -- `δ ≤ δ_EG`: every admissible set in [ErGr80] gives a nonzero value.
    obtain ⟨A, hA, hadm, hx⟩ := deltaEG_mem N
    rw [hx]
    refine delta_le_gap hA ?_
    intro h0
    exact hadm A (Finset.Subset.refl A) (by linarith [abs_eq_zero.mp h0])
  · rcases Nat.lt_or_ge N 3 with hN | hN
    · -- Small cases `N ≤ 2`, using the bound `δ(N) ≥ 1/[1,…,N]`.
      refine le_trans ?_ (one_div_lcm_le_delta N)
      interval_cases N
      · simpa using deltaEG_le (one_mem_valuesEG 0)
      · simpa using deltaEG_le (one_mem_valuesEG 1)
      · have hlcm : (Finset.Icc 1 2).lcm id = 2 := by decide
        rw [hlcm]
        refine deltaEG_le ⟨{2}, by decide, ?_, by norm_num⟩
        intro S hS
        rcases Finset.subset_singleton_iff.mp hS with rfl | rfl <;> norm_num
    · -- `N ≥ 3`: a minimizer of `δ(N)` is admissible, since `δ(N) < 1/N`.
      obtain ⟨h0, A, hA, hx⟩ := delta_mem N
      refine deltaEG_le ⟨A, hA, ?_, hx⟩
      intro S hS hS1
      have hlt := delta_lt_inv hN
      by_cases hSA : S = A
      · subst hSA
        exact h0 (by rw [hx, hS1, sub_self, abs_zero])
      · obtain ⟨m, hmA, hmS⟩ : ∃ m ∈ A, m ∉ S :=
          Finset.not_subset.mp fun hAS => hSA (Finset.Subset.antisymm hS hAS)
        have hm := Finset.mem_Icc.mp (hA hmA)
        have hsplit : ∑ n ∈ A \ S, (1 : ℝ) / n + ∑ n ∈ S, (1 : ℝ) / n
            = ∑ n ∈ A, (1 : ℝ) / n := Finset.sum_sdiff hS
        have hle : (1 : ℝ) / m ≤ ∑ n ∈ A \ S, (1 : ℝ) / n :=
          Finset.single_le_sum (f := fun n : ℕ => (1 : ℝ) / n)
            (fun n _ => by positivity) (Finset.mem_sdiff.mpr ⟨hmA, hmS⟩)
        have hmN : (1 : ℝ) / N ≤ 1 / m :=
          one_div_le_one_div_of_le (by exact_mod_cast hm.1) (by exact_mod_cast hm.2)
        have : (1 : ℝ) / N ≤ erdos311Delta N := by
          rw [hx, abs_sub_comm, ← hsplit, hS1]
          rw [abs_of_nonneg (by linarith [show (0 : ℝ) ≤ 1 / (m : ℝ) by positivity])]
          linarith
        linarith

/-- The open question is the same in both formulations (the website formulation and that of [ErGr80]). -/
theorem conjecture_iff_EG :
    Erdos311Conjecture ↔ ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ N ≥ 1, erdos311DeltaEG N = Real.exp (-(c + ε N) * N) := by
  simp only [Erdos311Conjecture, delta_eq_deltaEG]

end Erdos311

end

