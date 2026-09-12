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
# Erdős Problem 449

*References:*
- [erdosproblems.com/449](https://www.erdosproblems.com/449)
- [erdosproblems.com/448](https://www.erdosproblems.com/448) (the negative solution used here)
- [OEIS A397433](https://oeis.org/A397433): the integer sequence $\tau^+(n)$.
- [ErGr80] Erdős, P. and Graham, R. L., *Old and new problems and results in combinatorial
  number theory.* Monogr. Enseign. Math. **28** (1980), p. 89.
- [ErTe81] Erdős, P., Tenenbaum, G., *Sur la structure de la suite des diviseurs d'un entier.*
  Ann. Inst. Fourier (Grenoble) **31** (1981), 17–37.
- [HaTe88] Hall, R. R. and Tenenbaum, G., *Divisors.* (1988), §4.6.
-/

namespace Erdos449

open Finset

/-- `tauPlus n` (written $\tau^+(n)$) counts the number of $k$ such that $n$ has a divisor in
$[2^k, 2^{k+1})$; equivalently the number of distinct values of `Nat.log 2 d` as `d` ranges over
the divisors of `n`. Same definition as in `ErdosProblems/448`. -/
def tauPlus (n : ℕ) : ℕ := (n.divisors.image (Nat.log 2)).card

/-- The pairs of divisors counted by $r(n)$: ordered pairs $(d_1, d_2)$ of divisors of `n` with
$d_1 < d_2 < 2 d_1$. -/
def closePairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (n.divisors ×ˢ n.divisors).filter fun p => p.1 < p.2 ∧ p.2 < 2 * p.1

/-- $r(n)$ counts the pairs $d_1 \mid n$, $d_2 \mid n$ with $d_1 < d_2 < 2 d_1$. -/
def r (n : ℕ) : ℕ := (closePairs n).card

/-- The divisors of `n` lying in the dyadic block $[2^k, 2^{k+1})$. -/
def block (n k : ℕ) : Finset ℕ := n.divisors.filter fun d => Nat.log 2 d = k

/-- The set of dyadic blocks actually occupied by a divisor of `n`. Its cardinality is
`tauPlus n`. -/
def blocks (n : ℕ) : Finset ℕ := n.divisors.image (Nat.log 2)

/- ### Sanity checks (exact arithmetic, kernel-checked) -/

/-- $n = 6$: divisors $1,2,3,6$; the only pair with $d_1 < d_2 < 2d_1$ is $(2,3)$. -/
@[category test, AMS 11]
theorem r_six : r 6 = 1 := by decide

/-- $n = 12$: divisors $1,2,3,4,6,12$; the pairs are $(2,3), (3,4), (4,6)$. -/
@[category test, AMS 11]
theorem r_twelve : r 12 = 3 := by decide

/-- $\tau^+(12) = 4$ (dyadic blocks $0,1,1,2,2,3$). -/
@[category test, AMS 11]
theorem tauPlus_twelve : tauPlus 12 = 4 := by decide

/- ### The key lemma

Two distinct divisors in the *same* dyadic block are automatically a pair counted by $r$.
This is the whole arithmetic content of the argument. -/

/-- If $d_1 < d_2$ lie in the same dyadic block, i.e. `Nat.log 2 d₁ = Nat.log 2 d₂`, then
$d_2 < 2 d_1$. Indeed $2^k \le d_1$ and $d_2 < 2^{k+1} = 2 \cdot 2^k \le 2 d_1$. -/
@[category test, AMS 11]
theorem lt_two_mul_of_log_eq {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (_hlt : d₁ < d₂)
    (hlog : Nat.log 2 d₁ = Nat.log 2 d₂) : d₂ < 2 * d₁ := by
  have hlow : 2 ^ Nat.log 2 d₁ ≤ d₁ := Nat.pow_log_le_self 2 h₁.ne'
  have hhigh : d₂ < 2 ^ (Nat.log 2 d₂ + 1) := Nat.lt_pow_succ_log_self (by norm_num) d₂
  calc d₂ < 2 ^ (Nat.log 2 d₂ + 1) := hhigh
    _ = 2 * 2 ^ Nat.log 2 d₂ := by rw [pow_succ, mul_comm]
    _ = 2 * 2 ^ Nat.log 2 d₁ := by rw [hlog]
    _ ≤ 2 * d₁ := Nat.mul_le_mul_left 2 hlow

/-- The strictly increasing pairs inside one block. -/
def blockLt (n k : ℕ) : Finset (ℕ × ℕ) :=
  ((block n k) ×ˢ (block n k)).filter fun p => p.1 < p.2

/-- Every strictly increasing pair inside a single block is a pair counted by $r(n)$. -/
@[category test, AMS 11]
theorem blockLt_subset_closePairs (n k : ℕ) : blockLt n k ⊆ closePairs n := by
  intro p hp
  simp only [blockLt, block, closePairs, mem_filter, mem_product] at hp ⊢
  obtain ⟨⟨⟨h₁, hk₁⟩, ⟨h₂, hk₂⟩⟩, hlt⟩ := hp
  refine ⟨⟨h₁, h₂⟩, hlt, ?_⟩
  exact lt_two_mul_of_log_eq (Nat.pos_of_mem_divisors h₁) hlt (hk₁.trans hk₂.symm)

/- ### Bookkeeping

Two purely combinatorial steps, then Cauchy–Schwarz. -/

/-- Inside one block: $m_k^2 = 2 \cdot \#\{(d_1,d_2) : d_1 < d_2\} + m_k$, by splitting the
square `D ×ˢ D` into the diagonal and the two strict halves, which are swapped by
`Prod.swap`. -/
@[category test, AMS 11]
theorem card_sq_eq (D : Finset ℕ) :
    D.card ^ 2 = 2 * ((D ×ˢ D).filter fun p => p.1 < p.2).card + D.card := by
  classical
  -- The strict pairs `p.1 < p.2` and `p.2 < p.1` are equinumerous, via `Prod.swap`.
  have hLG : ((D ×ˢ D).filter fun p => p.1 < p.2).card
           = ((D ×ˢ D).filter fun p => p.2 < p.1).card := by
    apply Finset.card_bij (fun p _ => Prod.swap p)
    · intro p hp
      simp only [mem_filter, mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro a _ b _ hab
      simpa using congrArg Prod.swap hab
    · intro p hp
      refine ⟨Prod.swap p, ?_, by simp⟩
      simp only [mem_filter, mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  -- They are disjoint.
  have hdisj : Disjoint ((D ×ˢ D).filter fun p => p.1 < p.2)
                        ((D ×ˢ D).filter fun p => p.2 < p.1) := by
    apply Finset.disjoint_left.2
    intro p hp hq
    simp only [mem_filter] at hp hq
    exact absurd hp.2 (asymm hq.2)
  -- Split `D ×ˢ D` into the diagonal and the off-diagonal.
  have hsplit : (D ×ˢ D).card
      = ((D ×ˢ D).filter fun p => p.1 = p.2).card
      + ((D ×ˢ D).filter fun p => ¬ p.1 = p.2).card :=
    (Finset.card_filter_add_card_filter_not (s := D ×ˢ D) fun p => p.1 = p.2).symm
  have hdiagc : ((D ×ˢ D).filter fun p => p.1 = p.2).card = D.card := by
    apply Finset.card_bij (fun p _ => p.1)
    · intro p hp
      simp only [mem_filter, mem_product] at hp
      exact hp.1.1
    · intro a ha b hb hab
      simp only [mem_filter, mem_product] at ha hb
      rw [Prod.ext_iff]
      exact ⟨hab, by rw [← ha.2, ← hb.2]; exact hab⟩
    · intro d hd
      exact ⟨(d, d), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hd, hd⟩, rfl⟩, rfl⟩
  have hne2 : ((D ×ˢ D).filter fun p => ¬ p.1 = p.2).card
            = 2 * ((D ×ˢ D).filter fun p => p.1 < p.2).card := by
    have heq : ((D ×ˢ D).filter fun p => ¬ p.1 = p.2)
         = ((D ×ˢ D).filter fun p => p.1 < p.2)
         ∪ ((D ×ˢ D).filter fun p => p.2 < p.1) := by
      rw [← Finset.filter_or]
      apply Finset.filter_congr
      intro p _
      constructor
      · intro h; exact lt_or_gt_of_ne h
      · rintro (h | h)
        · exact h.ne
        · exact h.ne'
    rw [heq, Finset.card_union_of_disjoint hdisj, ← hLG]; ring
  rw [Finset.card_product] at hsplit
  rw [sq]; omega

/-- The blocks are pairwise disjoint, so the strict pairs they contain are pairwise disjoint
subsets of `closePairs n`; hence their total count is at most $r(n)$. -/
@[category test, AMS 11]
theorem sum_blockLt_card_le (n : ℕ) :
    ∑ k ∈ blocks n, (blockLt n k).card ≤ r n := by
  classical
  -- The blocks are pairwise disjoint: a pair in `blockLt n k` has first coordinate with
  -- `Nat.log 2` equal to `k`, so it cannot also lie in `blockLt n k'` for `k ≠ k'`.
  have hdisj : (blocks n : Set ℕ).PairwiseDisjoint (blockLt n) := by
    intro k _ k' _ hne
    simp only [Function.onFun]
    apply Finset.disjoint_left.2
    intro p hp hp'
    simp only [blockLt, block, mem_filter, mem_product] at hp hp'
    exact hne (hp.1.1.2.symm.trans hp'.1.1.2)
  -- Sum of cardinalities = cardinality of the disjoint union.
  rw [← Finset.card_biUnion hdisj]
  -- The disjoint union is contained in `closePairs n`.
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_biUnion] at hp
  obtain ⟨k, _, hpk⟩ := hp
  exact blockLt_subset_closePairs n k hpk

/-- The divisor count splits over the occupied blocks: $\sum_k m_k = \tau(n)$. -/
@[category test, AMS 11]
theorem sum_block_card (n : ℕ) :
    ∑ k ∈ blocks n, (block n k).card = n.divisors.card :=
  (Finset.card_eq_sum_card_image (Nat.log 2) n.divisors).symm

/- ### The inequality of Ford

This is the statement that appears on erdosproblems.com/449, in the form that the dyadic-block
Cauchy–Schwarz argument actually produces. Note the factor `2` in front of `r n`: the page as of
2026-08-28 states `r n + τ n ≥ τ n ^ 2 / τ⁺ n`, which fails already at `n = 6`
(`r = 1`, `τ = 4`, `τ⁺ = 3`, so `r + τ = 5 < 16/3`). -/

/-- **Ford's inequality.** $\tau^+(n)\,(2 r(n) + \tau(n)) \ge \tau(n)^2$, stated multiplicatively
to stay in `ℕ`. Combined with the negative solution of Erdős Problem 448 (which gives
$\tau^+(n) < \varepsilon \tau(n)$ on a set of positive density), this forces
$r(n) > K \tau(n)$ on a set of positive density, for every `K`. -/
@[category test, AMS 11]
theorem sq_card_divisors_le (n : ℕ) :
    n.divisors.card ^ 2 ≤ tauPlus n * (2 * r n + n.divisors.card) := by
  classical
  -- Cauchy–Schwarz over the occupied blocks.
  have hCS : (∑ k ∈ blocks n, (block n k).card) ^ 2
      ≤ (blocks n).card * ∑ k ∈ blocks n, (block n k).card ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  -- Rewrite each square inside one block.
  have hsq : ∑ k ∈ blocks n, (block n k).card ^ 2
      = 2 * (∑ k ∈ blocks n, (blockLt n k).card) + n.divisors.card := by
    rw [← sum_block_card n, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => card_sq_eq (block n k)
  calc n.divisors.card ^ 2
      = (∑ k ∈ blocks n, (block n k).card) ^ 2 := by rw [sum_block_card]
    _ ≤ (blocks n).card * ∑ k ∈ blocks n, (block n k).card ^ 2 := hCS
    _ = tauPlus n * (2 * (∑ k ∈ blocks n, (blockLt n k).card) + n.divisors.card) := by
        rw [hsq]; rfl
    _ ≤ tauPlus n * (2 * r n + n.divisors.card) := by
        exact Nat.mul_le_mul_left _ (by
          have := sum_blockLt_card_le n
          omega)

/- ### The problem itself -/

/--
Let $r(n)$ count the number of $d_1, d_2$ such that $d_1 \mid n$ and $d_2 \mid n$ and
$d_1 < d_2 < 2 d_1$. Is it true that, for every $\epsilon > 0$,
$$ r(n) < \epsilon \tau(n) $$
for almost all $n$, where $\tau(n)$ is the number of divisors of $n$?

This is false: for any constant $K > 0$ we have $r(n) > K \tau(n)$ for a positive density set of
$n$. Kevin Ford observed that this follows from the negative solution to Erdős Problem 448 via
`sq_card_divisors_le` above; the same argument is given for an essentially identical problem by
Hall and Tenenbaum [HaTe88, §4.6].
-/
@[category research solved, AMS 11]
theorem erdos_449 : answer(False) ↔
    ∀ ε : ℝ, 0 < ε →
      {n : ℕ | (r n : ℝ) < ε * (n.divisors.card : ℝ)}.HasDensity 1 := by
  sorry

/--
Quantitative form of the negative answer: for every `K`, the set of `n` with
$r(n) > K \tau(n)$ has positive lower density.
-/
@[category research solved, AMS 11]
theorem erdos_449.variants.positive_density (K : ℝ) :
    0 < {n : ℕ | K * (n.divisors.card : ℝ) < (r n : ℝ)}.lowerDensity := by
  sorry

end Erdos449
