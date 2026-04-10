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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 868

*Reference:* [erdosproblems.com/868](https://www.erdosproblems.com/868)
-/

open Filter

open scoped Pointwise

namespace Erdos868

/-- The number of ways in which a natural `n` can be written as the sum of
`o` members of the set `A`. -/
noncomputable
def ncard_add_repr (A : Set ℕ) (o : ℕ) (n : ℕ) : ℕ :=
  { a : Fin o → ℕ | Set.range a ⊆ A ∧ ∑ i, a i = n }.ncard

/-- Let $A$ be an additive basis of order $2$, let $f(n)$ denote the number of ways in which
$n$ can be written as the sum of two elements from $A$. If $f(n) \to \infty$ as $n \to \infty$, then
must $A$ contain a minimal additive basis of order $2$? -/
@[category research open, AMS 5 11]
theorem erdos_868.parts.i :
    answer(sorry) ↔ ∀ (A : Set ℕ), A.IsAsymptoticAddBasisOfOrder 2 →
      atTop.Tendsto (fun n => ncard_add_repr A 2 n) atTop → ∃ B ⊆ A,
      B.IsAsymptoticAddBasisOfOrder 2 ∧ ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

/-- Let $A$ be an additive basis of order $2$, let $f(n)$ denote the number of ways in which
$n$ can be written as the sum of two elements from $A$. If $f(n) > \epsilon \log n$ for large $n$
and an arbitrary fixed $\epsilon > 0$, then must $A$ contain a minimal additive
basis of order $2$? -/
@[category research open, AMS 5 11]
theorem erdos_868.parts.ii :
    answer(sorry) ↔ ∀ᵉ (A : Set ℕ) (ε > 0), A.IsAsymptoticAddBasisOfOrder 2 →
      (∀ᶠ (n : ℕ) in atTop, ε * Real.log n < ncard_add_repr A 2 n) → ∃ B ⊆ A,
      B.IsAsymptoticAddBasisOfOrder 2 ∧ ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

/-- Erdős and Nathanson proved that this is true if $f(n) > (\log \frac{4}{3})^{-1} \log n$ for
all large $n$. -/
@[category research solved, AMS 5 11]
theorem erdos_868.variants.fixed_ε :
    answer(True) ↔ ∀ (A : Set ℕ), A.IsAsymptoticAddBasisOfOrder 2 →
      (∀ᶠ (n : ℕ) in atTop, (Real.log (4 / 3))⁻¹ * Real.log n < ncard_add_repr A 2 n) → ∃ B ⊆ A,
      B.IsAsymptoticAddBasisOfOrder 2 ∧ ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

private lemma sum_mod_eq_sum_indicator_mod {o : ℕ} (f : Fin o → ℕ)
    (hf : ∀ i, f i = 1 ∨ o ∣ f i) :
    Finset.univ.sum f % o = (Finset.univ.sum fun i => if f i = 1 then 1 else 0) % o := by
  classical
  let g : Fin o → ℕ := fun i => if f i = 1 then 1 else 0
  have hfg : ∀ i ∈ Finset.univ, f i ≡ g i [MOD o] := by
    intro i hi
    rcases hf i with hfi | hfi
    · simp [g, hfi, Nat.ModEq]
    · rcases hfi with ⟨d, hd⟩
      have hf0 : f i % o = 0 := by simp [hd]
      have hg0 : g i % o = 0 := by
        by_cases h : o = 1 /\ d = 1
        · rcases h with ⟨rfl, rfl⟩
          simp [g, hd]
        · simp [g, hd, h]
      exact hf0.trans hg0.symm
  simpa [g, Nat.ModEq] using (Nat.ModEq.sum (s := Finset.univ) hfg)

private lemma sum_range_lt_indicator {r m : ℕ} :
    (Finset.range m).sum (fun i => if i < r then (1 : ℕ) else 0) = min m r := by
  induction m with
  | zero => simp
  | succ m hm =>
      rw [Finset.sum_range_succ, hm]
      by_cases hmr : m < r
      · simp [hmr, Nat.min_eq_left (Nat.le_of_lt hmr)]
      · have hrm : r ≤ m := Nat.le_of_not_lt hmr
        simp [hmr, Nat.min_eq_right hrm, Nat.min_eq_right (le_trans hrm (Nat.le_succ m))]

private lemma sum_range_prefix_const {r m c : ℕ} (hrm : r ≤ m) :
    (Finset.range m).sum (fun i => if i < r then (1 : ℕ) else c) = r + (m - r) * c := by
  rw [← Nat.add_sub_of_le hrm, Finset.sum_range_add]
  have hleft : (Finset.range r).sum (fun i => if i < r then (1 : ℕ) else c) = r := by
    calc
      (Finset.range r).sum (fun i => if i < r then (1 : ℕ) else c)
          = (Finset.range r).sum (fun _ => (1 : ℕ)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [Finset.mem_range.mp hi]
      _ = r := by
          simp
  have hright :
      (Finset.range (m - r)).sum (fun i => if r + i < r then (1 : ℕ) else c) = (m - r) * c := by
    calc
      (Finset.range (m - r)).sum (fun i => if r + i < r then (1 : ℕ) else c)
          = (Finset.range (m - r)).sum (fun _ => c) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have : ¬ r + i < r := by omega
              simp [this]
      _ = (m - r) * c := by
          simp
  rw [hleft, hright]
  simp [Nat.add_sub_of_le hrm]
/-- Härtter and Nathanson proved that there exist additive bases which do not contain
any minimal additive bases. -/
@[category research solved, AMS 5 11]
theorem erdos_868.variants.Hartter_Nathanson (o : ℕ) (ho : 1 < o) : ∃ (A : Set ℕ),
    A.IsAsymptoticAddBasisOfOrder o ∧ ∀ B ⊆ A, B.IsAsymptoticAddBasisOfOrder o →
    ∃ b ∈ B, (B \ {b}).IsAsymptoticAddBasisOfOrder o := by
  classical
  let A : Set ℕ := ({1} : Set ℕ) ∪ {n : ℕ | o ∣ n}
  have ho_pos : 0 < o := lt_trans Nat.zero_lt_one ho
  have hA_basis : A.IsAddBasisOfOrder o := by
    rw [Set.isAddBasisOfOrder_iff]
    intro n
    let r : ℕ := n % o
    let f : Fin o → ℕ := fun i =>
      if (i : ℕ) < r then 1 else if (i : ℕ) = o - 1 then n - r else 0
    refine ⟨f, ?_, ?_⟩
    · intro i
      by_cases hi : (i : ℕ) < r
      · left
        simp [f, hi]
      · by_cases hlast : (i : ℕ) = o - 1
        · have hnotlt : ¬ o - 1 < r := by
            simpa [hlast] using hi
          right
          refine ⟨n / o, ?_⟩
          have hdiv : n - r = o * (n / o) := by
            dsimp [r]
            have hmoddiv := Nat.mod_add_div n o
            omega
          simpa [f, hlast, hnotlt] using hdiv
        · right
          simp [f, hi, hlast]
    · have hr_lt : r < o := by
        dsimp [r]
        exact Nat.mod_lt _ ho_pos
      have hr_le : r ≤ o - 1 := by
        omega
      rw [Fin.sum_univ_eq_sum_range (fun i => if i < r then (1 : ℕ) else if i = o - 1 then n - r else 0)]
      rw [← Nat.succ_pred_eq_of_pos ho_pos, Finset.sum_range_succ]
      have hprefix :
          (Finset.range (o - 1)).sum (fun i => if i < r then (1 : ℕ) else 0) = r := by
        simpa [min_eq_right hr_le] using sum_range_lt_indicator (r := r) (m := o - 1)
      have hprefix' :
          (∑ x ∈ Finset.range (o - 1), if x < r then (1 : ℕ) else if x = o - 1 then n - r else 0) = r := by
        calc
          (∑ x ∈ Finset.range (o - 1), if x < r then (1 : ℕ) else if x = o - 1 then n - r else 0)
              = ∑ x ∈ Finset.range (o - 1), if x < r then (1 : ℕ) else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  have hx_ne : x ≠ o - 1 := by
                    have hx_lt : x < o - 1 := Finset.mem_range.mp hx
                    omega
                  simp [hx_ne]
          _ = r := hprefix
      have hlast : ¬ o - 1 < r := by omega
      have hprefix'' :
          (∑ x ∈ Finset.range o.pred, if x < r then (1 : ℕ) else if x = o.pred.succ - 1 then n - r else 0) = r := by
        simpa [Nat.succ_pred_eq_of_pos ho_pos, Nat.succ_eq_add_one] using hprefix'
      rw [hprefix'']
      simp [hlast]
      dsimp [r]
      have hmoddiv := Nat.mod_add_div n o
      omega
  refine ⟨A, hA_basis.isAsymptoticAddBasisOfOrder, ?_⟩
  intro B hBA hB
  have hBsum := (Set.isAsymptoticAddBasisOfOrder_iff_sum_atTop).1 hB
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hBsum
  have h1B : (1 : ℕ) ∈ B := by
    by_contra h1B
    have hBdvd : ∀ x ∈ B, o ∣ x := by
      intro x hx
      have hxA : x ∈ A := hBA hx
      simp [A] at hxA
      rcases hxA with rfl | hxA
      · exact False.elim (h1B hx)
      · exact hxA
    have hlarge : N ≤ o * N + 1 := by
      exact (Nat.le_mul_of_pos_left N ho_pos).trans (Nat.le_succ _)
    have hrepr := hN (o * N + 1) hlarge
    rcases hrepr with ⟨f, hfB, hsum⟩
    have hdivsum : o ∣ ∑ i, f i := by
      simpa using (Finset.dvd_sum (s := Finset.univ) (f := fun i : Fin o => f i)
        (a := o) (fun i hi => hBdvd (f i) (hfB i)))
    have hdiv : o ∣ o * N + 1 := by simpa [hsum] using hdivsum
    have hzero : (o * N + 1) % o = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hone : (o * N + 1) % o = 1 := by
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt ho]
    omega
  have hmult : ∃ K, ∀ k ≥ K, o * k ∈ B := by
    refine ⟨N, ?_⟩
    intro k hk
    have hlarge : N ≤ o * k + (o - 1) := by
      calc
        N ≤ k := hk
        _ ≤ o * k := Nat.le_mul_of_pos_left k ho_pos
        _ ≤ o * k + (o - 1) := Nat.le_add_right _ _
    have hrepr := hN (o * k + (o - 1)) hlarge
    rcases hrepr with ⟨f, hfB, hsum⟩
    have hfA : ∀ i, f i ∈ A := fun i => hBA (hfB i)
    have hf_cases : ∀ i, f i = 1 ∨ o ∣ f i := by
      intro i
      have hfi : f i ∈ A := hfA i
      simp [A] at hfi
      exact hfi
    let ones : ℕ := ∑ i, if f i = 1 then 1 else 0
    have hmod : (∑ i, f i) % o = ones % o := by
      dsimp [ones]
      exact sum_mod_eq_sum_indicator_mod f hf_cases
    have hones_mod : ones % o = o - 1 := by
      rw [← hmod, hsum]
      have hlt : o - 1 < o := by omega
      simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]
    have hones_le : ones ≤ o := by
      dsimp [ones]
      calc
        (∑ i, if f i = 1 then 1 else 0) ≤ ∑ i : Fin o, (1 : ℕ) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          by_cases hfi : f i = 1 <;> simp [hfi]
        _ = o := by simp
    have hones_ne : ones ≠ o := by
      intro hone
      have : 0 = o - 1 := by
        simpa [hone, ho_pos.ne'] using hones_mod
      omega
    have hones_lt : ones < o := by
      exact Nat.lt_of_le_of_ne hones_le hones_ne
    have hones_eq : ones = o - 1 := by
      rw [Nat.mod_eq_of_lt hones_lt] at hones_mod
      exact hones_mod
    have hones_filter : ∑ i ∈ Finset.univ with f i = 1, (1 : ℕ) = o - 1 := by
      have : ones = ∑ i ∈ Finset.univ with f i = 1, (1 : ℕ) := by
        dsimp [ones]
        symm
        simpa [Finset.mem_filter] using
          (Finset.sum_ite_mem_eq (s := Finset.univ.filter fun i : Fin o => f i = 1)
            (f := fun _ => (1 : ℕ)))
      omega
    have hnotone_filter : ∑ i ∈ Finset.univ with f i ≠ 1, (1 : ℕ) = 1 := by
      have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun i : Fin o => f i = 1) (f := fun _ => (1 : ℕ))
      have htotal : (∑ _i : Fin o, (1 : ℕ)) = o := by simp
      have hsplit' :
          (∑ i ∈ Finset.univ with f i = 1, (1 : ℕ)) +
            (∑ i ∈ Finset.univ with f i ≠ 1, (1 : ℕ)) = o := by
        simpa using hsplit.trans htotal
      omega
    have hcard_notone : (Finset.univ.filter fun i : Fin o => f i ≠ 1).card = 1 := by
      simpa using hnotone_filter
    rcases Finset.card_eq_one.mp hcard_notone with ⟨j, hj⟩
    have hj_ne_one : f j ≠ 1 := by
      have : j ∈ Finset.univ.filter fun i : Fin o => f i ≠ 1 := by simp [hj]
      simpa [Finset.mem_filter] using this
    have hrest : ∀ i, i ≠ j → f i = 1 := by
      intro i hij
      by_contra hi
      have hi_mem : i ∈ Finset.univ.filter fun t : Fin o => f t ≠ 1 := by
        simp [Finset.mem_filter, hi]
      have : i = j := by
        rw [hj] at hi_mem
        simpa using hi_mem
      exact hij this
    have hsum_erase : ∑ x ∈ Finset.univ.erase j, f x = o - 1 := by
      have hcongr : ∑ x ∈ Finset.univ.erase j, f x = ∑ x ∈ Finset.univ.erase j, (1 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hx_ne : x ≠ j := by
          have hx' := hx
          simp [Finset.mem_erase] at hx'
          exact hx'
        exact hrest x hx_ne
      rw [hcongr]
      simp
    have hsum_split : f j + ∑ x ∈ Finset.univ.erase j, f x = ∑ i, f i := by
      simpa using (Finset.add_sum_erase (s := Finset.univ) (f := fun i : Fin o => f i)
        (by simp : j ∈ Finset.univ))
    have hfj : f j = o * k := by
      have hsum_data := hsum
      have herase_data := hsum_erase
      have hsplit_data := hsum_split
      omega
    simpa [hfj] using hfB j
  rcases hmult with ⟨K, hmultK⟩
  let b : ℕ := o * K
  have hbB : b ∈ B := by
    dsimp [b]
    exact hmultK K le_rfl
  refine ⟨b, hbB, ?_⟩
  rw [Set.isAsymptoticAddBasisOfOrder_iff_sum_atTop]
  let M : ℕ := o * o * (K + 1) + (o - 1)
  refine Filter.eventually_atTop.2 ⟨M, ?_⟩
  intro n hn
  dsimp [M] at hn
  let r : ℕ := n % o
  let c : ℕ := o * (K + 1)
  let t : ℕ := n / o - (o - 1 - r) * (K + 1)
  let f : Fin o → ℕ := fun i =>
    if (i : ℕ) < r then 1 else if (i : ℕ) = o - 1 then o * t else c
  refine ⟨f, ?_, ?_⟩
  · intro i
    dsimp [f]
    by_cases hi : (i : ℕ) < r
    · constructor
      · simpa [f, hi] using h1B
      · simp [hi, b]
        rcases Nat.eq_zero_or_pos K with rfl | hKpos
        · simp
        · have ho_two : 2 ≤ o := by omega
          have htwo : 2 ≤ o * K := by
            exact le_trans ho_two (Nat.le_mul_of_pos_right o hKpos)
          omega
    · by_cases hlast : (i : ℕ) = o - 1
      · have ht_ge : K + 1 ≤ t := by
          have hr_lt : r < o := by
            dsimp [r]
            exact Nat.mod_lt _ ho_pos
          have hbase : o * o * (K + 1) ≤ n := by
            omega
          have hdiv_lower : o * (K + 1) ≤ n / o := by
            refine (Nat.le_div_iff_mul_le ho_pos).2 ?_
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbase
          have hcoeff : o - 1 - r + 1 ≤ o := by
            omega
          have haux : ((o - 1 - r) + 1) * (K + 1) ≤ o * (K + 1) := by
            exact Nat.mul_le_mul_right (K + 1) hcoeff
          let u : ℕ := o - 1 - r
          have haux' : K + 1 + (o - 1 - r) * (K + 1) ≤ o * (K + 1) := by
            calc
              K + 1 + (o - 1 - r) * (K + 1)
                  = K + 1 + u * (K + 1) := by simp [u]
              _ = (u + 1) * (K + 1) := by ring
              _ ≤ o * (K + 1) := by simpa [u] using haux
          dsimp [t]
          exact Nat.le_sub_of_add_le (le_trans haux' hdiv_lower)
        have hnotlt : ¬ o - 1 < r := by
          simpa [hlast] using hi
        have htB : o * t ∈ B := hmultK t (le_trans (Nat.le_succ K) ht_ge)
        constructor
        · simpa [f, hi, hlast, hnotlt] using htB
        · simp [hlast, hnotlt, b]
          constructor
          · intro hEq
            omega
          · exact ho_pos.ne'
      · have hcB : c ∈ B := by
          dsimp [c]
          exact hmultK (K + 1) (Nat.le_succ K)
        constructor
        · simpa [f, hi, hlast] using hcB
        · simpa [f, hi, hlast, b, c] using ho_pos.ne'
  · dsimp [f]
    have hr_lt : r < o := by
      dsimp [r]
      exact Nat.mod_lt _ ho_pos
    have hr_le : r ≤ o - 1 := by omega
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < r then (1 : ℕ) else if i = o - 1 then o * t else c)]
    rw [← Nat.succ_pred_eq_of_pos ho_pos, Finset.sum_range_succ]
    have hprefix :
        (Finset.range (o - 1)).sum (fun i => if i < r then (1 : ℕ) else c) =
          r + (o - 1 - r) * c := by
      simpa [c] using sum_range_prefix_const (r := r) (m := o - 1) (c := c) hr_le
    have hprefix' :
        (∑ x ∈ Finset.range (o - 1), if x < r then (1 : ℕ) else if x = o - 1 then (o - 1 + 1) * t else c) =
          r + (o - 1 - r) * c := by
      calc
        (∑ x ∈ Finset.range (o - 1), if x < r then (1 : ℕ) else if x = o - 1 then (o - 1 + 1) * t else c)
            = ∑ x ∈ Finset.range (o - 1), if x < r then (1 : ℕ) else c := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                have hx_ne : x ≠ o - 1 := by
                  have hx_lt : x < o - 1 := Finset.mem_range.mp hx
                  omega
                simp [hx_ne]
        _ = r + (o - 1 - r) * c := hprefix
    have hlast : ¬ o - 1 < r := by omega
    have hprefix'' :
        (∑ x ∈ Finset.range o.pred, if x < r then (1 : ℕ) else if x = o.pred.succ - 1 then o.pred.succ * t else c) =
          r + (o - 1 - r) * c := by
      simpa [Nat.succ_pred_eq_of_pos ho_pos] using hprefix'
    rw [hprefix'']
    simp [hlast]
    dsimp [t, c, r]
    have ho_eq : o - 1 + 1 = o := by omega
    rw [ho_eq]
    change n % o + (o - 1 - n % o) * (o * (K + 1)) + o * (n / o - (o - 1 - n % o) * (K + 1)) = n
    let d : ℕ := (o - 1 - n % o) * (K + 1)
    have hbase : o * o * (K + 1) ≤ n := by
      omega
    have hdiv_lower : o * (K + 1) ≤ n / o := by
      refine (Nat.le_div_iff_mul_le ho_pos).2 ?_
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbase
    have hd_coeff : o - 1 - n % o ≤ o := by
      have hmodlt : n % o < o := Nat.mod_lt _ ho_pos
      omega
    have hd_le : d ≤ n / o := by
      dsimp [d]
      exact (Nat.mul_le_mul_right (K + 1) hd_coeff).trans hdiv_lower
    have hcancel : d * o + o * (n / o - d) = o * (n / o) := by
      calc
        d * o + o * (n / o - d) = o * d + o * (n / o - d) := by
          simp [Nat.mul_comm]
        _ = o * (d + (n / o - d)) := by rw [← Nat.mul_add]
        _ = o * (n / o) := by rw [Nat.add_sub_of_le hd_le]
    calc
      n % o + (o - 1 - n % o) * (o * (K + 1)) + o * (n / o - (o - 1 - n % o) * (K + 1))
          = n % o + (d * o + o * (n / o - d)) := by
              simp [d, Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]
      _ = n % o + o * (n / o) := by rw [hcancel]
      _ = n := Nat.mod_add_div n o

end Erdos868
