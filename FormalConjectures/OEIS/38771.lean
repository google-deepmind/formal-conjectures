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
# Smallest composite $c$ such that $\textrm{primorial}(n) + c$ is prime

*References:*
- [A038771](https://oeis.org/A038771)
-/

open Filter Topology Real



namespace OeisA38771

/-- $a(n)$ is the smallest composite number $c$ such that $\textrm{primorial}(n) + c$ is prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  let Qn : ℕ := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i
  let is_composite (c : ℕ) : Prop := c > 1 ∧ ¬ c.Prime
  sInf { c : ℕ | is_composite c ∧ (Qn + c).Prime }

@[category test, AMS 11]
theorem a_0 : a 0 = 4 := by
  change sInf { c : ℕ | (c > 1 ∧ ¬ c.Prime) ∧
    ((∏ i ∈ Finset.range 0, Nat.nth Nat.Prime i) + c).Prime } = 4
  have hQ : (∏ i ∈ Finset.range 0, Nat.nth Nat.Prime i) = 1 := by rfl
  rw [hQ]
  have h_least : IsLeast { c : ℕ | (c > 1 ∧ ¬ c.Prime) ∧ (1 + c).Prime } 4 := by
    refine ⟨⟨⟨by decide, by decide⟩, by decide⟩, ?_⟩
    intro c hc
    by_contra! hlt
    interval_cases c <;> revert hc <;> decide
  exact h_least.csInf_eq

@[category test, AMS 11]
theorem a_1 : a 1 = 9 := by
  change sInf { c : ℕ | (c > 1 ∧ ¬ c.Prime) ∧
    ((∏ i ∈ Finset.range 1, Nat.nth Nat.Prime i) + c).Prime } = 9
  have hQ : (∏ i ∈ Finset.range 1, Nat.nth Nat.Prime i) = 2 := by
    rw [Finset.prod_range_one, Nat.nth_prime_zero_eq_two]
  rw [hQ]
  have h_least : IsLeast { c : ℕ | (c > 1 ∧ ¬ c.Prime) ∧ (2 + c).Prime } 9 := by
    refine ⟨⟨⟨by decide, by decide⟩, by decide⟩, ?_⟩
    intro c hc
    by_contra! hlt
    interval_cases c <;> revert hc <;> decide
  exact h_least.csInf_eq

@[category test, AMS 11]
theorem a_2 : a 2 = 25 := by
  change sInf { c : ℕ | (c > 1 ∧ ¬ c.Prime) ∧
    ((∏ i ∈ Finset.range 2, Nat.nth Nat.Prime i) + c).Prime } = 25
  have hQ : (∏ i ∈ Finset.range 2, Nat.nth Nat.Prime i) = 6 := by
    rw [Finset.prod_range_succ, Finset.prod_range_one,
      Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
    rfl
  rw [hQ]
  have h_least : IsLeast { c : ℕ | (c > 1 ∧ ¬ c.Prime) ∧ (6 + c).Prime } 25 := by
    refine ⟨⟨⟨by decide, by decide⟩, by decide⟩, ?_⟩
    intro c hc
    by_contra! hlt
    interval_cases c <;> revert hc <;> decide
  exact h_least.csInf_eq

@[category test, AMS 11]
theorem a_3 : a 3 = 49 := by
  change sInf { c : ℕ | (c > 1 ∧ ¬ c.Prime) ∧
    ((∏ i ∈ Finset.range 3, Nat.nth Nat.Prime i) + c).Prime } = 49
  have hQ : (∏ i ∈ Finset.range 3, Nat.nth Nat.Prime i) = 30 := by
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one,
      Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
    rfl
  rw [hQ]
  have h_least : IsLeast { c : ℕ | (c > 1 ∧ ¬ c.Prime) ∧ (30 + c).Prime } 49 := by
    refine ⟨⟨⟨by decide, by decide⟩, by decide⟩, ?_⟩
    intro c hc
    by_contra! hlt
    interval_cases c <;> revert hc <;> decide
  exact h_least.csInf_eq

/--
$a(n) \ne 0$ for all $n$ (i.e., a suitable composite $c$ always exists).
The following more general statement follows from Dirichlet's theorem
on primes in arithmetic progressions:
  there doesn't exist a > 0 natural number such that p - a is prime for every prime p > a.

Choose q prime such that q is coprime with a, and p > a + q prime such that q | p - a
(such a p exists from Dirichlet's theorem). Then p - a is composite, a contradiction.
-/
@[category textbook, AMS 11]
theorem a_n_exists (n : ℕ) : a n ≠ 0 := by
  sorry

/--
Conjecture:
$\liminf_{n \to \infty} \frac{a(n)}{p_{n+1}^2} = 1 <$
$\limsup_{n \to \infty} \frac{a(n)}{p_{n+1}^2} = 2$.
- Charles R Greathouse IV and Thomas Ordowski, Apr 24 2015
-/
@[category research open, AMS 11]
theorem conjecture1 :
    let p_next_sq (n : ℕ) : ℝ := ((Nat.nth Nat.Prime n : ℝ)) ^ 2
    let seq (n : ℕ) : ℝ := (a n : ℝ) / p_next_sq n
    (liminf seq atTop = 1) ∧ (limsup seq atTop = 2) := by
  sorry

/--
All the terms in this sequence have exactly two prime factors.
This conjecture is true for the first 133 terms.
- [Dmitry Kamenetsky](https://oeis.org/wiki/User:Dmitry_Kamenetsky), Jan 06 2019
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ a n = p * q := by
  sorry

end OeisA38771
