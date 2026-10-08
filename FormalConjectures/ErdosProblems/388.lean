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
# Erdős Problem 388

*Reference:* [erdosproblems.com/388](https://www.erdosproblems.com/388)
-/

@[expose] public section

open scoped BigOperators
namespace Erdos388

/-- The product of the k consecutive positive integers immediately after m. -/
def blockProduct (m k : ℕ) : ℕ := ∏ i ∈ Finset.range k, (m + i + 1)

/-- Original unweighted equation, with both lengths strictly larger than 3. -/
def IsSolution (m₁ k₁ m₂ k₂ : ℕ) : Prop :=
  3 < k₁ ∧ 3 < k₂ ∧ m₁ + k₁ ≤ m₂ ∧
    blockProduct m₁ k₁ = blockProduct m₂ k₂

/-- Global finiteness, with both lengths varying in the set of quadruples. -/
def FinitenessConjecture : Prop :=
  Set.Finite {q : ℕ × ℕ × ℕ × ℕ | IsSolution q.1 q.2.1 q.2.2.1 q.2.2.2}

/-- Fixed-pair finiteness is a separate, weaker target. -/
def FixedLengthsFinite (k₁ k₂ : ℕ) : Prop :=
  Set.Finite {q : ℕ × ℕ | IsSolution q.1 k₁ q.2 k₂}

@[category API, AMS 11]
theorem block_product_pos (m k : ℕ) : 0 < blockProduct m k := by
  unfold blockProduct
  exact Finset.prod_pos (fun i _ => by omega)

@[category API, AMS 11]
theorem block_product_strictMono {k : ℕ} (hk : 0 < k) :
    StrictMono (fun m => blockProduct m k) := by
  intro m n hmn
  unfold blockProduct
  apply Finset.prod_lt_prod_of_nonempty
  · intro i _
    omega
  · intro i _
    omega
  · exact ⟨0, Finset.mem_range.mpr hk⟩

@[category API, AMS 11]
theorem block_product_monotone_length (m : ℕ) : Monotone (blockProduct m) := by
  apply monotone_nat_of_le_succ
  intro k
  unfold blockProduct
  rw [Finset.prod_range_succ]
  have hfactor : 1 ≤ m + k + 1 := by omega
  exact le_mul_of_one_le_right (Nat.zero_le _) hfactor

@[category API, AMS 11]
theorem IsSolution.length_lt {m₁ k₁ m₂ k₂ : ℕ}
    (h : IsSolution m₁ k₁ m₂ k₂) : k₂ < k₁ := by
  rcases h with ⟨hk₁, hk₂, hsep, heq⟩
  by_contra hnot
  have hlen : k₁ ≤ k₂ := by omega
  have hm : m₁ < m₂ := by omega
  have hstrict : blockProduct m₁ k₁ < blockProduct m₂ k₁ :=
    block_product_strictMono (by omega) hm
  have hmono := block_product_monotone_length m₂ hlen
  omega

@[category API, AMS 11]
theorem IsSolution.length_ne {m₁ k₁ m₂ k₂ : ℕ}
    (h : IsSolution m₁ k₁ m₂ k₂) : k₁ ≠ k₂ := by
  have := h.length_lt
  omega

@[category API, AMS 11]
theorem not_is_solution_equal_lengths (m₁ m₂ k : ℕ) :
    ¬ IsSolution m₁ k m₂ k := by
  intro h
  exact (Nat.lt_irrefl k) h.length_lt

/-- Each entry in a block divides its product. -/
@[category API, AMS 11]
theorem factor_dvd_block_product {m k i : ℕ} (hi : i < k) :
    m + i + 1 ∣ blockProduct m k := by
  exact Finset.dvd_prod_of_mem (fun j : ℕ => m + j + 1) (Finset.mem_range.mpr hi)

/-- A prime divides a block product exactly when it divides one of its entries. -/
@[category API, AMS 11]
theorem prime_dvd_block_product_iff {m k p : ℕ} (hp : Nat.Prime p) :
    p ∣ blockProduct m k ↔ ∃ i < k, p ∣ m + i + 1 := by
  simpa only [blockProduct, Finset.mem_range] using
    (hp.prime.dvd_finsetProd_iff (fun i : ℕ => m + i + 1)
      (S := Finset.range k))

/-- Every prime divisor of a block product is at most the block's last entry. -/
@[category API, AMS 11]
theorem prime_le_last_of_dvd_block_product {m k p : ℕ}
    (hp : Nat.Prime p) (hdiv : p ∣ blockProduct m k) : p ≤ m + k := by
  obtain ⟨i, hi, hpi⟩ := (prime_dvd_block_product_iff hp).mp hdiv
  have hle : p ≤ m + i + 1 := Nat.le_of_dvd (by omega) hpi
  omega

/-- In a solution, every prime dividing an entry of the right block is bounded
by the last entry of the left block. -/
@[category API, AMS 11]
theorem right_factor_prime_le_left_last {m₁ k₁ m₂ k₂ j p : ℕ}
    (h : IsSolution m₁ k₁ m₂ k₂) (hj : j < k₂)
    (hp : Nat.Prime p) (hdiv : p ∣ m₂ + j + 1) : p ≤ m₁ + k₁ := by
  have hprod : p ∣ blockProduct m₂ k₂ :=
    dvd_trans hdiv (factor_dvd_block_product hj)
  have heq : blockProduct m₁ k₁ = blockProduct m₂ k₂ := h.2.2.2
  rw [← heq] at hprod
  exact prime_le_last_of_dvd_block_product hp hprod

/-- The blocks $8,\ldots,14$ and $63,\ldots,66$ have equal products. -/
@[category test, AMS 11]
theorem known_solution : IsSolution 7 7 62 4 := by
  norm_num [IsSolution, blockProduct, Finset.prod_range_succ]

/-- Pairing the eight factors at equal distance from the ends gives four quadratics. -/
@[category test, AMS 11]
theorem eight_factor_decomposition (x : ℤ) :
    x * (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) =
      (x * (x + 7)) * (x * (x + 7) + 6) *
        (x * (x + 7) + 10) * (x * (x + 7) + 12) := by
  ring

/-- A product of four consecutive positive integers is one less than a square. -/
@[category test, AMS 11]
theorem four_factor_square (m : ℕ) :
    blockProduct m 4 + 1 = (m * m + 5 * m + 5) ^ 2 := by
  simp [blockProduct, Finset.prod_range_succ]
  ring

/-- A length-three block can always be represented by a later length-one block.
This only concerns a relaxed equation; its lengths do not satisfy `IsSolution`. -/
@[category test, AMS 11]
theorem three_one_family (m : ℕ) :
    m + 3 ≤ blockProduct m 3 - 1 ∧
      blockProduct m 3 = blockProduct (blockProduct m 3 - 1) 1 := by
  have hp : blockProduct m 3 = (m + 1) * (m + 2) * (m + 3) := by
    simp [blockProduct, Finset.prod_range_succ, Nat.add_assoc]
  have hlow : m + 4 ≤ blockProduct m 3 := by
    rw [hp]
    nlinarith [Nat.zero_le (m * m * m)]
  constructor
  · omega
  · have hone (n : ℕ) : blockProduct n 1 = n + 1 := by
      simp [blockProduct]
    rw [hone]
    omega

/--
Can one classify all solutions of
$$\prod_{1\leq i\leq k_1}(m_1+i)=\prod_{1\leq j\leq k_2}(m_2+j)$$
where $k_1,k_2>3$ and $m_1+k_1\leq m_2$?
The offsets are nonnegative, so every factor is positive.
-/
@[category research open, AMS 11]
theorem erdos_388.parts.i :
    {q : ℕ × ℕ × ℕ × ℕ | IsSolution q.1 q.2.1 q.2.2.1 q.2.2.2} = answer(sorry) := by
  sorry

/--
Are there only finitely many solutions of
$$\prod_{1\leq i\leq k_1}(m_1+i)=\prod_{1\leq j\leq k_2}(m_2+j)$$
where $k_1,k_2>3$ and $m_1+k_1\leq m_2$?
Both lengths vary; finiteness for each fixed pair of lengths is a weaker statement.
-/
@[category research open, AMS 11]
theorem erdos_388.parts.ii : answer(sorry) ↔
    Set.Finite {q : ℕ × ℕ × ℕ × ℕ | IsSolution q.1 q.2.1 q.2.2.1 q.2.2.2} := by
  sorry

end Erdos388
