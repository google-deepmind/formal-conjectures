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
# Rowland's GCD prime-generating recurrence

Define $a(1) = 7$ and $a(n) = a(n - 1) + \gcd(n, a(n - 1))$ for $n \ge 2$ (`OEIS A106108`), with
step increments $d(n) = a(n) - a(n - 1) = \gcd(n, a(n - 1))$ (`OEIS A132199` lists $d(n + 1)$ for
$n \ge 1$). Eric S. Rowland established in 2008 that every $d(n)$ with $n \ge 2$ equals $1$ or an
odd prime, and conjectured that every odd prime arises as $d(n)$ for some $n \ge 2$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Formula_for_primes#Rowland%27s_prime-generating_sequence)
- [OEIS A106108](https://oeis.org/A106108)
- [OEIS A132199](https://oeis.org/A132199)
- E. S. Rowland, *A natural prime-generating recurrence*, J. Integer Seq. **11** (2008),
  Article 08.2.8.
-/

@[expose] public section

namespace RowlandSequence

/-- Rowland's sequence (`OEIS A106108`), starting at $a(1) = 7$ with recurrence
$a(n) = a(n - 1) + \gcd(n, a(n - 1))$ for $n \ge 2$ (and $a(0) = 0$). -/
def rowlandSeq : ℕ → ℕ
  | 0 => 0
  | 1 => 7
  | n + 2 =>
    let prev := rowlandSeq (n + 1)
    prev + Nat.gcd (n + 2) prev

/-- Step increment $d(n) = a(n) - a(n - 1)$ of `rowlandSeq` (meaningful for $n \ge 2$; shifted by
one from `OEIS A132199`, where `A132199(n) = rowlandDiff (n + 1)`). -/
def rowlandDiff (n : ℕ) : ℕ :=
  rowlandSeq n - rowlandSeq (n - 1)

/-- Checks the initial values $a(1), \dots, a(6) = 7, 8, 9, 10, 15, 18$ of `rowlandSeq`. -/
@[category test, AMS 11]
theorem rowlandSeq_initial_values :
    rowlandSeq 1 = 7 ∧ rowlandSeq 2 = 8 ∧ rowlandSeq 3 = 9 ∧
      rowlandSeq 4 = 10 ∧ rowlandSeq 5 = 15 ∧ rowlandSeq 6 = 18 := by
  decide

/-- Checks $d(2) = 1$ alongside the odd-prime increments $d(5) = 5$, $d(6) = 3$, and
$d(11) = 11$. -/
@[category test, AMS 11]
theorem rowlandDiff_small_witnesses :
    rowlandDiff 2 = 1 ∧ rowlandDiff 5 = 5 ∧ rowlandDiff 6 = 3 ∧ rowlandDiff 11 = 11 := by
  decide

/-- Key gcd computation: if `m = 2c - 1` has least prime factor `p`, then for `c < j` with
`2j - m ≤ p`, `gcd(j, m)` is `1`, unless `2j - m = p`, in which case it is `p`. -/
@[category API, AMS 11]
lemma gcd_eq_one_or_minFac {c j : ℕ} (hc : 3 ≤ c) (hj : c < j)
    (hjp : 2 * j - (2 * c - 1) ≤ (2 * c - 1).minFac) :
    Nat.gcd j (2 * c - 1) = if 2 * j - (2 * c - 1) = (2 * c - 1).minFac then (2 * c - 1).minFac
      else 1 := by
  set m := 2 * c - 1 with hm
  have hm1 : m ≠ 1 := by omega
  have hp := Nat.minFac_prime hm1
  set g := Nat.gcd j m
  have hgd : g ∣ 2 * j - m := Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _)
    (Nat.gcd_dvd_right _ _)
  split_ifs with heq
  · -- `p ∣ 2j`, `p` odd, so `p ∣ j`; and `g ∣ p`
    have hmodd : Odd m := ⟨c - 1, by omega⟩
    have hp2 : m.minFac ≠ 2 := fun h2 => by
      have := Nat.minFac_dvd m; rw [h2] at this
      exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr this)
    have hpj : m.minFac ∣ j := by
      have h2j : m.minFac ∣ 2 * j := by
        have : 2 * j = (2 * j - m) + m := by omega
        rw [this, heq]; exact dvd_add dvd_rfl (Nat.minFac_dvd m)
      exact (Nat.Prime.dvd_mul hp).mp h2j |>.resolve_left fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    exact Nat.dvd_antisymm (heq ▸ hgd) (Nat.dvd_gcd hpj (Nat.minFac_dvd m))
  · by_contra hg1
    have hq := Nat.minFac_prime hg1
    have hqm : m.minFac ≤ g.minFac :=
      Nat.minFac_le_of_dvd hq.two_le ((Nat.minFac_dvd g).trans (Nat.gcd_dvd_right _ _))
    have hpos : 0 < 2 * j - m := by omega
    have hq2 : g.minFac ≤ 2 * j - m := Nat.le_of_dvd hpos ((Nat.minFac_dvd g).trans hgd)
    omega

/-- The recurrence of `rowlandSeq` for `n ≥ 1`. -/
@[category API, AMS 11]
lemma rowlandSeq_succ {n : ℕ} (hn : 1 ≤ n) :
    rowlandSeq (n + 1) = rowlandSeq n + Nat.gcd (n + 1) (rowlandSeq n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rfl

/-- The invariant: `n` lies in a segment starting at some `c ≥ 3` with `a(c) = 3c`, in which
`a(n) = n + 2c` and the segment has not ended yet. -/
@[category API, AMS 11]
lemma segment (n : ℕ) (hn : 3 ≤ n) : ∃ c, 3 ≤ c ∧ c ≤ n ∧ rowlandSeq n = n + 2 * c ∧
    2 * (n + 1) - (2 * c - 1) ≤ (2 * c - 1).minFac := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨3, le_rfl, le_rfl, by decide, by norm_num⟩
  | succ n hn ih =>
    obtain ⟨c, hc, hcn, ha, hlen⟩ := ih
    have hstep := rowlandSeq_succ (n := n) (by omega)
    have hg : Nat.gcd (n + 1) (rowlandSeq n) = Nat.gcd (n + 1) (2 * c - 1) := by
      rw [ha, show n + 2 * c = (2 * c - 1) + (n + 1) by omega, Nat.gcd_add_self_right]
    have key := gcd_eq_one_or_minFac hc (show c < n + 1 by omega) hlen
    by_cases heq : 2 * (n + 1) - (2 * c - 1) = (2 * c - 1).minFac
    · -- the segment ends: restart at `c' = n + 1`
      refine ⟨n + 1, by omega, le_rfl, ?_, ?_⟩
      · have h1 : rowlandSeq (n + 1) = n + 2 * c + (2 * c - 1).minFac := by
          rw [hstep, hg, key, if_pos heq, ha]
        omega
      · have hp := Nat.minFac_prime (show 2 * (n + 1) - 1 ≠ 1 by omega)
        have hodd : (2 * (n + 1) - 1).minFac ≠ 2 := fun h2 => by
          have := Nat.minFac_dvd (2 * (n + 1) - 1); rw [h2] at this; omega
        have := hp.two_le
        omega
    · have hpo : (2 * c - 1).minFac % 2 = 1 := by
        have h := Nat.minFac_dvd (2 * c - 1)
        rcases (Nat.minFac_prime (by omega : 2 * c - 1 ≠ 1)).eq_two_or_odd with h2 | h2
        · rw [h2] at h; omega
        · exact h2
      refine ⟨c, hc, by omega, ?_, by omega⟩
      have h1 : rowlandSeq (n + 1) = n + 2 * c + 1 := by
        rw [hstep, hg, key, if_neg heq, ha]
      omega

/--
Rowland's theorem (2008): for every $n \ge 2$, the step $d(n) = a(n) - a(n - 1)$ equals $1$ or is
prime.
-/
@[category research solved, AMS 11]
theorem rowland_diff_eq_one_or_prime {n : ℕ} (hn : 2 ≤ n) :
    rowlandDiff n = 1 ∨ (rowlandDiff n).Prime := by
  rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn4
  · left; decide
  · left; decide
  obtain ⟨c, hc, hcn, ha, hlen⟩ := segment (n - 1) (by omega)
  have hstep := rowlandSeq_succ (n := n - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hstep hlen
  have hg : Nat.gcd n (rowlandSeq (n - 1)) = Nat.gcd n (2 * c - 1) := by
    rw [ha, show n - 1 + 2 * c = (2 * c - 1) + n by omega, Nat.gcd_add_self_right]
  have key := gcd_eq_one_or_minFac hc (by omega : c < n) hlen
  have hd : rowlandDiff n = Nat.gcd n (2 * c - 1) := by
    unfold rowlandDiff
    rw [hstep, hg]
    omega
  rw [hd, key]
  split_ifs
  · exact Or.inr (Nat.minFac_prime (by omega))
  · exact Or.inl rfl

/--
Rowland's conjecture (2008): every odd prime $p$ occurs as $d(n) = a(n) - a(n - 1)$ at some index
$n \ge 2$. The prime $2$ is excluded because $n$ and $a(n - 1)$ always have opposite parity, and
$n \ge 2$ excludes the artifact `rowlandDiff 1 = 7`.
-/
@[category research open, AMS 11]
theorem rowland_generates_all_odd_primes {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ∃ n : ℕ, 2 ≤ n ∧ rowlandDiff n = p := by
  sorry

end RowlandSequence
