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
# Erdős Problem 954

*References:*
- [erdosproblems.com/954](https://www.erdosproblems.com/954)
- [Er77c] Erdős, P., *Problems and results on combinatorial number theory. III*. Number theory
  day (Proc. Conf., Rockefeller Univ., New York, 1976), Lecture Notes in Math. 626, Springer
  (1977), 43-72. [PDF](https://www.renyi.hu/~p_erdos/1977-27.pdf)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos954

/-- `pairCount a m n` is the number of pairs `(i, j)` with `0 ≤ i ≤ j ≤ m`, `1 ≤ j` and
`a i + a j ≤ n`. -/
def pairCount (a : ℕ → ℕ) (m n : ℕ) : ℕ :=
  ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧ a p.1 + a p.2 ≤ n).card

/-- Stage `k` of the construction of Rosen's sequence: `rosenAux k i = a_i` for `i ≤ k + 1`.

Stage `0` holds `a_0 = 0` and `a_1 = 1` (the value `1` at the unused indices `i ≥ 2` is a
placeholder). Stage `k + 1` appends `a_{k+2}`, the least `n` such that the number of pairs
`(i, j)` with `0 ≤ i ≤ j ≤ k + 1`, `1 ≤ j` and `a_i + a_j ≤ n` is less than `n`. This count is
below `(k + 2) ^ 2`, so the set is nonempty and `sInf` is a genuine minimum. -/
noncomputable def rosenAux : ℕ → ℕ → ℕ
  | 0 => fun i => if i = 0 then 0 else 1
  | k + 1 => fun i =>
      if i = k + 2 then sInf {n : ℕ | pairCount (rosenAux k) (k + 1) n < n} else rosenAux k i

/-- Rosen's sequence $a_0=0$, $a_1=1$, $a_{k+1}=\min\{n : \#\{(i,j) : 0\le i\le j\le k,\ j\ge 1,
a_i+a_j\le n\} < n\}$. It begins $0,1,3,5,9,13,17,24,31,38,45,\ldots$ -/
noncomputable def rosen (k : ℕ) : ℕ := rosenAux k k

/-- The number of solutions of $a_i+a_j\le x$ with $0\le i\le j$ and $j\ge 1$, over the whole
sequence `rosen`. The sequence is strictly increasing with `rosen 0 = 0`, so `rosen j ≥ j`.
Hence a pair with `rosen i + rosen j ≤ x` has `j ≤ x`, and counting the pairs with `j ≤ x`
counts all solutions. -/
noncomputable def solutionCount (x : ℕ) : ℕ := pairCount rosen x x

@[category test, AMS 11]
theorem rosen_zero : rosen 0 = 0 := by
  decide

@[category test, AMS 11]
theorem rosen_one : rosen 1 = 1 := by
  decide

@[category test, AMS 11]
theorem rosen_two : rosen 2 = 3 := by
  show sInf {n : ℕ | pairCount (rosenAux 0) 1 n < n} = 3
  exact IsLeast.csInf_eq (by decide)

/-- Stage `k` of `rosenAux` agrees with `rosen` on all indices `i ≤ k + 1`. -/
@[category API, AMS 11]
theorem rosenAux_eq_rosen : ∀ {k i : ℕ}, i ≤ k + 1 → rosenAux k i = rosen i
  | 0, 0, _ => rfl
  | 0, 1, _ => rosen_one.symm
  | 0, _ + 2, hi => by omega
  | k + 1, i, hi => by
    rcases Nat.of_le_succ hi with hik | rfl
    · change (if i = k + 2 then _ else rosenAux k i) = rosen i
      rw [if_neg (by omega)]; exact rosenAux_eq_rosen hik
    · change _ = rosenAux (k + 2) (k + 2)
      symm
      change (if k + 2 = k + 3 then _ else rosenAux (k + 1) (k + 2)) = _
      rw [if_neg (by omega)]

/-- Replacing `rosenAux k` by `rosen` does not change `pairCount` up to index `k + 1`. -/
@[category API, AMS 11]
theorem pairCount_rosenAux_eq (k n : ℕ) :
    pairCount (rosenAux k) (k + 1) n = pairCount rosen (k + 1) n := by
  unfold pairCount
  congr 1
  refine Finset.filter_congr fun ⟨i, j⟩ hmem => ?_
  simp only [Finset.mem_product, Finset.mem_range] at hmem
  rw [rosenAux_eq_rosen (by omega), rosenAux_eq_rosen (by omega)]

/-- `pairCount` is monotone in the index bound and the threshold. -/
@[category API, AMS 11]
theorem pairCount_mono {a : ℕ → ℕ} {m₁ m₂ n₁ n₂ : ℕ} (hm : m₁ ≤ m₂) (hn : n₁ ≤ n₂) :
    pairCount a m₁ n₁ ≤ pairCount a m₂ n₂ := by
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
  exact ⟨⟨by omega, by omega⟩, hp.2.1, hp.2.2.1, le_trans hp.2.2.2 hn⟩

/-- Unfolds `rosen (k + 2)` directly to the stage-`k` infimum defining `a_{k+2}`. -/
@[category API, AMS 11]
theorem rosen_add_two (k : ℕ) :
    rosen (k + 2) = sInf {n : ℕ | pairCount (rosenAux k) (k + 1) n < n} := by
  rw [← rosenAux_eq_rosen (le_rfl : k + 2 ≤ (k + 1) + 1)]
  change (if k + 2 = k + 2 then _ else _) = _
  rw [if_pos rfl]

/-- Rosen's sequence is strictly increasing, justifying the definition of `solutionCount`. -/
@[category API, AMS 11]
theorem rosen_strictMono : StrictMono rosen := by
  have hne (a : ℕ → ℕ) (m : ℕ) : {n : ℕ | pairCount a m n < n}.Nonempty :=
    ⟨(m + 1) * (m + 1) + 1, Nat.lt_succ_of_le <| by
      simpa [pairCount, Finset.card_product, Finset.card_range] using Finset.card_filter_le
        (Finset.range (m + 1) ×ˢ Finset.range (m + 1))
        (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧ a p.1 + a p.2 ≤ (m + 1) * (m + 1) + 1)⟩
  refine strictMono_nat_of_lt_succ fun k => ?_
  match k with
  | 0 => rw [rosen_zero, rosen_one]; omega
  | 1 => rw [rosen_one, rosen_two]; omega
  | m + 2 =>
    have hdef2 := rosen_add_two m
    set N := rosen (m + 2)
    have hN1 : 1 ≤ N := by
      rw [hdef2]; exact le_csInf (hne _ _) fun b hb => by change pairCount _ _ b < b at hb; omega
    rw [rosen_add_two (m + 1)]
    show N + 1 ≤ sInf {n : ℕ | pairCount (rosenAux (m + 1)) (m + 2) n < n}
    refine le_csInf (hne _ _) fun b hb => ?_
    change pairCount (rosenAux (m + 1)) (m + 2) b < b at hb
    rw [pairCount_rosenAux_eq] at hb
    change pairCount rosen (m + 2) b < b at hb
    by_contra hle
    rcases lt_or_eq_of_le (show b ≤ N by omega) with hlt | rfl
    · have hge : b ≤ pairCount (rosenAux m) (m + 1) b := le_of_not_gt fun hmem => by
        have := csInf_le (OrderBot.bddBelow _)
          (show b ∈ {n : ℕ | pairCount (rosenAux m) (m + 1) n < n} from hmem); omega
      rw [pairCount_rosenAux_eq] at hge
      exact absurd (hge.trans (pairCount_mono (Nat.le_succ _) le_rfl)) (not_le_of_gt hb)
    · have hprev : N - 1 ≤ pairCount (rosenAux m) (m + 1) (N - 1) := le_of_not_gt fun hmem => by
        have := csInf_le (OrderBot.bddBelow _)
          (show N - 1 ∈ {n : ℕ | pairCount (rosenAux m) (m + 1) n < n} from hmem); omega
      rw [pairCount_rosenAux_eq] at hprev
      have hprevN : N - 1 ≤ pairCount rosen (m + 1) N :=
        hprev.trans (pairCount_mono le_rfl (Nat.sub_le N 1))
      have hstrict : pairCount rosen (m + 1) N < pairCount rosen (m + 2) N := by
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨fun p hp => ?_, fun heq => ?_⟩)
        · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
          exact ⟨⟨by omega, by omega⟩, hp.2⟩
        · have hmem : ((0 : ℕ), m + 2) ∈ (Finset.range (m + 3) ×ˢ Finset.range (m + 3)).filter
              fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧ rosen p.1 + rosen p.2 ≤ N := by
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
              rosen_zero, zero_add]
            exact ⟨⟨by omega, by omega⟩, by omega, by omega, le_rfl⟩
          rw [← heq] at hmem
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hmem; omega
      omega

/--
Let $0=a_0<a_1<a_2<\cdots$ be the sequence of integers defined by $a_0=0$ and $a_1=1$, and
$a_{k+1}$ is the smallest integer $n$ for which the number of solutions to $a_i+a_j \leq n$
(with $0\leq i\leq j\leq k$ and $j\geq 1$) is $<n$.

Is the number of solutions to $a_i+a_j \leq x$ equal to $x+O(x^{1/4+o(1)})$?

The sequence was constructed by Rosen [Er77c, p. 71]. We read $O(x^{1/4+o(1)})$ as
$O(x^{1/4+\varepsilon})$ for every $\varepsilon>0$, and use the version with $a_0=0$.
-/
@[category research open, question, AMS 11]
theorem erdos_954 :
    ∀ ε > (0 : ℝ), (fun x : ℕ ↦ (solutionCount x : ℝ) - x) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ ((1 : ℝ) / 4 + ε)) := by
  sorry

/--
Erdős and Rosen could not even prove that the number of solutions to $a_i+a_j\leq x$ is at most
$(1+o(1))x$ [Er77c, p. 71].
-/
@[category research open, AMS 11]
theorem erdos_954.variants.upper :
    ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop, (solutionCount x : ℝ) ≤ (1 + ε) * x := by
  sorry

/--
The number of solutions to $a_i+a_j\leq x$ is always at least $x$ by construction
[Er77c, p. 71].
-/
@[category textbook, AMS 11]
theorem erdos_954.variants.lower : ∀ x : ℕ, x ≤ solutionCount x := by
  intro x
  match x with
  | 0 => exact Nat.zero_le _
  | 1 =>
    unfold solutionCount pairCount
    refine Finset.card_pos.2 ⟨(0, 1), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, rosen_zero, rosen_one]
    omega
  | k + 2 =>
    have hgt : ∀ m, m + 2 < rosen (m + 2) := fun m => by
      induction m with
      | zero => rw [rosen_two]; omega
      | succ m ih =>
        show m + 3 < rosen (m + 3)
        have hlt := rosen_strictMono (show m + 2 < m + 3 by omega)
        omega
    have hdef := rosen_add_two k
    have hge : k + 2 ≤ pairCount (rosenAux k) (k + 1) (k + 2) := le_of_not_gt fun hmem => by
      have hcs := csInf_le (OrderBot.bddBelow _)
        (show k + 2 ∈ {n : ℕ | pairCount (rosenAux k) (k + 1) n < n} from hmem)
      have hgk := hgt k
      omega
    rw [pairCount_rosenAux_eq] at hge
    exact hge.trans (pairCount_mono (Nat.le_succ _) le_rfl)

end Erdos954
