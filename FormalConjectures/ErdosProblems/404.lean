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
# Erdős Problem 404

*References:*
- [erdosproblems.com/404](https://www.erdosproblems.com/404)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathématique (1980), p. 79.
-/

@[expose] public section

open scoped BigOperators
open Filter

namespace Erdos404

/-- The sum of the factorials indexed by a finite set. -/
def factorialSum (s : Finset ℕ) : ℕ := ∑ n ∈ s, n.factorial

/-- The least element of the finite set is $a$. -/
def StartsAt (a : ℕ) (s : Finset ℕ) : Prop := a ∈ s ∧ ∀ n ∈ s, a ≤ n

/-- Some sum of distinct factorials starting at $a!$ is divisible by $p^k$. -/
def Achievable (a p k : ℕ) : Prop :=
  ∃ s : Finset ℕ, StartsAt a s ∧ p ^ k ∣ factorialSum s

/-- The supremum of the attainable exponents, with $\infty$ for unbounded exponents. -/
noncomputable def f (a p : ℕ) : ℕ∞ :=
  sSup {v : ℕ∞ | ∃ k : ℕ, Achievable a p k ∧ v = (k : ℕ∞)}

@[category API, AMS 11]
theorem achievable_of_dvd_factorial {a p k : ℕ} (h : p ^ k ∣ a.factorial) :
    Achievable a p k := by
  refine ⟨{a}, ?_, ?_⟩
  · simp [StartsAt]
  · simpa [factorialSum] using h

@[category API, AMS 11]
theorem achievable_zero (a p : ℕ) : Achievable a p 0 := by
  exact achievable_of_dvd_factorial (by simp)

@[category API, AMS 11]
theorem le_f_of_achievable {a p k : ℕ} (h : Achievable a p k) : (k : ℕ∞) ≤ f a p := by
  exact le_sSup ⟨k, h, rfl⟩

@[category API, AMS 11]
theorem f_le_iff (a p K : ℕ) : f a p ≤ (K : ℕ∞) ↔ ∀ k, Achievable a p k → k ≤ K := by
  constructor
  · intro h k hk
    exact ENat.natCast_le_natCast.mp ((le_f_of_achievable hk).trans h)
  · intro h
    apply sSup_le
    rintro v ⟨k, hk, rfl⟩
    exact ENat.natCast_le_natCast.mpr (h k hk)

/--
For which integers $a\geq 1$ and primes $p$ is there a finite upper bound on those $k$
such that there are $a=a_1<\cdots<a_n$ with
$$p^k \mid (a_1!+\cdots+a_n!)?$$
-/
@[category research open, AMS 11]
theorem erdos_404.parts.i :
    {(a, p) : ℕ × ℕ | 1 ≤ a ∧ p.Prime ∧
      ∃ K : ℕ, ∀ k : ℕ, Achievable a p k → k ≤ K} = answer(sorry) := by
  sorry

/--
If $f(a,p)$ is the greatest such $k$, how does this function behave?

The function takes values in $\mathbb{N}\cup\{\infty\}$, allowing unbounded exponents.
-/
@[category research open, AMS 11]
theorem erdos_404.parts.ii :
    (fun (a : ℕ+) (p : Nat.Primes) => f a p) = answer(sorry) := by
  sorry

/-- The sum of the first $n+1$ factorials in a sequence. -/
def partialSum (u : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (u i).factorial

@[category API, AMS 11]
theorem partialSum_pos (u : ℕ → ℕ) (n : ℕ) : 0 < partialSum u n := by
  unfold partialSum
  exact Finset.sum_pos (fun i _ => Nat.factorial_pos (u i))
    (Finset.nonempty_range_iff.mpr (by omega))

/--
Is there a prime $p$ and an infinite sequence $a_1<a_2<\cdots$ such that if $p^{m_k}$
is the highest power of $p$ dividing $\sum_{i\leq k}a_i!$ then $m_k\to \infty$?

The sequence consists of positive integers, indexed from $0$ in Lean.
-/
@[category research open, AMS 11]
theorem erdos_404.parts.iii : answer(sorry) ↔
    ∃ p : ℕ, p.Prime ∧ ∃ u : ℕ → ℕ,
      StrictMono u ∧ 1 ≤ u 0 ∧
        Tendsto (fun n => padicValNat p (partialSum u n)) atTop atTop := by
  sorry

@[category API, AMS 11]
theorem valuation_tendsto_iff {p : ℕ} (hp : p.Prime) (u : ℕ → ℕ) :
    Tendsto (fun n => padicValNat p (partialSum u n)) atTop atTop ↔
      ∀ K : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → p ^ K ∣ partialSum u n := by
  let : Fact p.Prime := ⟨hp⟩
  rw [tendsto_atTop_atTop]
  simp only [padicValNat_dvd_iff_le (Nat.ne_of_gt (partialSum_pos u _))]

/-- For every prime $p$, the maximum exponent tends to infinity as the start tends to infinity. -/
@[category textbook, AMS 11]
theorem erdos_404.variants.eventual_lower_bound (p : ℕ) (hp : p.Prime) (K : ℕ) :
    ∃ A : ℕ, ∀ a : ℕ, A ≤ a → (K : ℕ∞) ≤ f a p := by
  have hpow (k : ℕ) : p ^ k ∣ (p * k).factorial := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Nat.mul_succ]
      exact (Nat.mul_dvd_mul ih (Nat.dvd_factorial hp.pos (le_refl p))).trans
        (Nat.factorial_mul_factorial_dvd_factorial_add (p * k) p)
  refine ⟨p * K, fun a ha => ?_⟩
  apply le_f_of_achievable
  apply achievable_of_dvd_factorial
  exact (hpow K).trans (Nat.factorial_dvd_factorial ha)

end Erdos404
