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
# Squarefree semiprimes

Numbers that are the product of two distinct primes.

*References:*
- [A006881](https://oeis.org/A006881)
-/

@[expose] public section

namespace OeisA6881

/-- The set of squarefree semiprimes. (Numbers that are the product of two distinct primes.) -/
def SquarefreeSemiprimes : Set ℕ := {n | n.IsSemiprime ∧ Squarefree n}

@[category API, AMS 11]
lemma mem_squarefreeSemiprimes {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    p * q ∈ SquarefreeSemiprimes := by
  exact ⟨hp.mul_isAlmostPrime_two hq,
    Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hp hq).2 hpq, hp.squarefree, hq.squarefree⟩⟩

@[category test, AMS 11]
theorem squarefreeSemiprimes_do_not_include_four : 4 ∉ SquarefreeSemiprimes := by
  change ¬ (Nat.IsSemiprime 4 ∧ Squarefree 4)
  rintro ⟨_, hs⟩
  exact (Nat.squarefree_iff_prime_squarefree.mp hs) 2 (by norm_num) (by norm_num)

@[category test, AMS 11]
theorem a_1 : 6 ∈ SquarefreeSemiprimes := by
  apply mem_squarefreeSemiprimes (p := 2) (q := 3) <;> norm_num

@[category test, AMS 11]
theorem a_2 : 10 ∈ SquarefreeSemiprimes := by
  apply mem_squarefreeSemiprimes (p := 2) (q := 5) <;> norm_num

@[category test, AMS 11]
theorem a_3 : 14 ∈ SquarefreeSemiprimes := by
  apply mem_squarefreeSemiprimes (p := 2) (q := 7) <;> norm_num

@[category test, AMS 11]
theorem a_4 : 15 ∈ SquarefreeSemiprimes := by
  apply mem_squarefreeSemiprimes (p := 3) (q := 5) <;> norm_num

@[category test, AMS 11]
theorem a_5 : 21 ∈ SquarefreeSemiprimes := by
  apply mem_squarefreeSemiprimes (p := 3) (q := 7) <;> norm_num

/--
"Conjecture: The sums of two elements of [the sequence of squarefree semiprimes] forms a set
that includes all primes greater than or equal to 29 and all integers greater than or
equal to 83 (and many below 83)."
- Richard R. Forberg, Mar 04 2015, [A006881](https://oeis.org/A006881)
-/
@[category research open, AMS 11]
theorem conjecture (k : ℕ) (hk : (29 ≤ k ∧ k.Prime) ∨ (83 ≤ k)) :
    ∃ m n : SquarefreeSemiprimes, k = m + n := by sorry

end OeisA6881
