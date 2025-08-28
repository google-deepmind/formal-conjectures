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

import Mathlib

def Nat.squarefreePart (n : ℕ) : ℕ :=
  ∏ p ∈ { q ∈ n.primeFactors | Odd (n.factorization q)}, p

def Nat.squarePart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (if Even <| n.factorization p then n.factorization p else n.factorization p - 1)

open Function

theorem Squarefree.prod_of_pairwise_isCoprime {R : Type*} [CancelCommMonoidWithZero R]
    [DecompositionMonoid R] {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → R}
    (hs : Set.Pairwise s (IsRelPrime on f)) (hs' : ∀ i ∈ s, Squarefree (f i)) :
    Squarefree (∏ i ∈ s, f i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, squarefree_mul_iff]
    rw [Finset.coe_insert, Set.pairwise_insert] at hs
    refine ⟨IsRelPrime.prod_right fun i hi ↦ ?_, hs' a (by simp), ?_⟩
    · exact (hs.right i (by simp [hi]) fun h ↦ ha (h ▸ hi)).left
    · exact ih hs.left fun i hi ↦ hs' i <| Finset.mem_insert_of_mem hi


theorem Nat.Prime.coprime_iff_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    p.Coprime q ↔ p ≠ q := by
  rw [hp.coprime_iff_not_dvd, hq.dvd_iff_eq (hp.ne_one), ne_comm]

theorem Nat.Prime.squarefree {p : ℕ} (hp : p.Prime) :
    Squarefree p := by
  exact Irreducible.squarefree hp

theorem Nat.squarefree_squarefreePart (n : ℕ) : Squarefree n.squarefreePart := by
  apply Squarefree.prod_of_pairwise_isCoprime
  · have : (n.primeFactors : Set ℕ).Pairwise (IsRelPrime on id)
    · intro p hp q hq hpq
      simp [Function.onFun]
      rwa [←Nat.coprime_iff_isRelPrime, (prime_of_mem_primeFactors hp).coprime_iff_ne
        (prime_of_mem_primeFactors hq)]
    apply Set.Pairwise.mono _ this
    rw [Finset.coe_subset]
    exact Finset.filter_subset _ _
  · intro i hi
    rw [Finset.mem_filter] at hi
    apply (prime_of_mem_primeFactors hi.left).squarefree


#check Nat.prod_factorization_eq_prod_primeFactors
#check Nat.prod_primeFactors_of_squarefree

theorem Nat.prod_primeFactors_eq {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
  conv_rhs => rw [←prod_primeFactorsList hn]
  rw [Finset.prod_list_count]
  apply Finset.prod_congr rfl
  simp

theorem Nat.squarefreePart_mul_squarePart (n : ℕ) (hn : n ≠ 0) : n.squarefreePart * n.squarePart = n := by
  have : n.squarefreePart = ∏ p ∈ n.primeFactors, p ^ (if Even <| n.factorization p then 0 else 1)
  · sorry
  unfold Nat.squarePart
  rw [this, ←Finset.prod_mul_distrib]
  have (hn : n ≠ 0) : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
    rw [Nat.prod_primeFactors_eq hn]
  conv_rhs =>
    rw [←Nat.prod_primeFactors_eq hn]
  apply Finset.prod_congr rfl
  intro p hp
  rw [←pow_add, ite_add_ite]
  congr 1
  rw [ite_eq_iff]
  by_cases H : Even (n.factorization p)
  · simp [H]
  · simp only [H, zero_add, and_true, not_false_eq_true, true_and, false_or]
    rw [Nat.add_comm, Nat.sub_add_cancel]
    exact ((prime_of_mem_primeFactors hp).dvd_iff_one_le_factorization hn).mp
      (dvd_of_mem_primeFactors hp)
