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
# Erdős Problem 983

*References:*
- [erdosproblems.com/983](https://www.erdosproblems.com/983)
- [Er70b] Erdős, P., Some applications of graph theory to number theory. Proc. Second Chapel Hill
  Conf. on Combinatorial Mathematics and its Applications (Univ. North Carolina, Chapel Hill,
  N.C., 1970) (1970), 136-145.
-/

open Filter Finset Asymptotics MeasureTheory Nat

open scoped Nat.Prime

namespace Erdos983

/--
An integer `a` is composed only of primes from `P` if every prime factor of `a` lies in `P`.
By convention this holds for `a = 1`, since `1` has no prime factors.
-/
abbrev IsComposedOf (P : Finset ℕ) (a : ℕ) : Prop :=
  a.primeFactors ⊆ P

/--
There exist `r` distinct primes such that more than `r` elements of `A` have all their prime
factors among those primes.
-/
def HasPrimeSupportExceeding (A : Finset ℕ) (r : ℕ) : Prop :=
  ∃ P : Finset ℕ, P.card = r ∧ (∀ p ∈ P, p.Prime) ∧
    r < (A.filter (IsComposedOf P)).card

/--
Let $n \ge 2$ and $\pi(n) < k \le n$. Let $f(k,n)$ be the smallest integer $r$ such that in any
$A \subseteq \{1,\ldots,n\}$ of size $|A| = k$ there exist primes $p_1,\ldots,p_r$ such that $> r$
many $a \in A$ are only divisible by primes from $\{p_1,\ldots,p_r\}$.

If no such $r$ exists then `f k n = 0`, which occurs for example when $k \le \pi(n)$.
-/
noncomputable def f (k n : ℕ) : ℕ :=
  sInf { r | ∀ A : Finset ℕ, A ⊆ Icc 1 n → A.card = k → HasPrimeSupportExceeding A r }

/-- `1` is composed of primes from any set, including the empty set. -/
@[category test, AMS 11]
theorem isComposedOf_one (P : Finset ℕ) : IsComposedOf P 1 := by
  simp [IsComposedOf]

/-- A prime is not composed of the empty set of primes. -/
@[category test, AMS 11]
theorem not_isComposedOf_empty_two : ¬ IsComposedOf ∅ 2 := by
  simp [IsComposedOf]

/-- The set $\{1,2\}$ has more than $0$ elements composed of the empty set of primes. -/
@[category test, AMS 11]
theorem hasPrimeSupportExceeding_one_two_zero :
    HasPrimeSupportExceeding {1, 2} 0 := by
  refine ⟨∅, rfl, by simp, ?_⟩
  have h : ({1, 2} : Finset ℕ).filter (IsComposedOf ∅) = {1} := by
    ext a
    simp [IsComposedOf, subset_empty, primeFactors_eq_empty]
    omega
  rw [h]
  decide

/--
Let $n \ge 2$ and $\pi(n) < k \le n$. Let $f(k,n)$ be the smallest integer $r$ such that in any
$A \subseteq \{1,\ldots,n\}$ of size $|A| = k$ there exist primes $p_1,\ldots,p_r$ such that $> r$
many $a \in A$ are only divisible by primes from $\{p_1,\ldots,p_r\}$.

Is it true that
$$
2\pi(n^{1/2}) - f(\pi(n)+1, n) \to \infty
$$
as $n \to \infty$?

In general, estimate $f(k,n)$, particularly when $\pi(n)+1 < k = o(n)$.
-/
@[category research open, AMS 11]
theorem erdos_983 :
    answer(sorry) ↔
      Tendsto (fun n : ℕ ↦ (2 * π (Nat.sqrt n) : ℝ) - f (π n + 1) n) atTop atTop := by
  sorry

/--
It is trivial that $f(k,n) \le \pi(n)$.
-/
@[category textbook, AMS 11]
theorem erdos_983.variants.trivial {k n : ℕ} (hk : π n < k) (_hkn : k ≤ n) :
    f k n ≤ π n := by
  refine Nat.sInf_le ?_
  intro A hA hcard
  refine ⟨n.primesLE, n.primesLE_card_eq_primeCounting, fun p hp ↦ prime_of_mem_primesLE hp, ?_⟩
  have hfilter : A.filter (IsComposedOf n.primesLE) = A := by
    ext a
    simp only [mem_filter, IsComposedOf, and_iff_left_iff_imp]
    intro ha p hp
    exact mem_primesLE.mpr ⟨(le_of_mem_primeFactors hp).trans (mem_Icc.mp (hA ha)).2,
      prime_of_mem_primeFactors hp⟩
  simpa [hfilter, hcard] using hk

/--
Erdős and Straus [Er70b] proved that
$$
f(\pi(n)+1, n) = 2\pi(n^{1/2}) + o_A\left(\frac{n^{1/2}}{(\log n)^A}\right)
$$
for any $A > 0$.
-/
@[category research solved, AMS 11]
theorem erdos_983.variants.sqrt_bound {A : ℝ} (hA : 0 < A) :
    (fun n : ℕ ↦ (f (π n + 1) n : ℝ) - 2 * π (Nat.sqrt n)) =o[atTop]
      fun n ↦ (n : ℝ).sqrt / (Real.log n) ^ A := by
  sorry

/--
Erdős and Straus [Er70b] proved that for any constant $1 > c > 0$,
$$
f(cn, n) = \log\log n + (c_1 + o(1))\sqrt{2\log\log n},
$$
where
$$
c = \frac{1}{\sqrt{2\pi}} \int_{-\infty}^{c_1} e^{-x^2/2}\, dx.
$$
-/
@[category research solved, AMS 11]
theorem erdos_983.variants.linear_density {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1) :
    ∃ c₁ : ℝ,
      (∫ x in Set.Iic c₁, Real.exp (-x ^ 2 / 2)) / (2 * Real.pi).sqrt = c ∧
      (fun n : ℕ ↦ (f ⌊c * n⌋₊ n : ℝ) - Real.log (Real.log n) -
        c₁ * (2 * Real.log (Real.log n)).sqrt) =o[atTop]
        fun n ↦ (2 * Real.log (Real.log n)).sqrt := by
  sorry

end Erdos983
