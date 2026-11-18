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
# Shanks's asymptotic conjecture for maximal prime gaps

Writing $p_n$ for the $n$-th prime ($0$-indexed, $p_0 = 2$) and $g_n = p_{n+1} - p_n$ (`primeGap n`)
for the $n$-th prime gap, let $G(x) = \max_{p_n < x} g_n$ (`sup_primeGap x`) denote the largest
prime gap starting below $x$ (which has the same asymptotic growth as $\max_{p_n \le x} g_n$). An
index $n$ marks a record (maximal) gap whenever $g_m < g_n$ for all $m < n$. Strengthening
Cramér's prime-gap heuristic, Daniel Shanks (1964) conjectured that $G(x) \sim (\log x)^2$ as
$x \to \infty$. By contrast, Andrew Granville's (1995) sieve-adjusted model predicts
$\limsup_{n \to \infty} g_n / (\log p_n)^2 \ge 2e^{-\gamma} \approx 1.1229$, contradicting
Shanks's conjecture. See also `Erdos5`.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Cram%C3%A9r%27s_conjecture#Shanks_conjecture)
- [Wikipedia: Prime gap](https://en.wikipedia.org/wiki/Prime_gap#Numerical_results)
- D. Shanks, *On maximal gaps between successive primes*, Math. Comp. **18** (1964), no. 88,
  646–651.
- A. Granville, *Harald Cramér and the distribution of prime numbers*, Scand. Actuar. J. **1995**
  (1995), no. 1, 12–28.
-/

@[expose] public section

open scoped Asymptotics

namespace MaximalPrimeGap

/-- Predicate that index $n$ achieves a strictly larger `primeGap` than all earlier indices
$m < n$. -/
def IsMaximalPrimeGapIndex (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → primeGap m < primeGap n

/-- Checks the first three indices and `sup_primeGap` at $x = 6$: $g_0 = 1$ and $g_1 = 2$ are
record gaps, $g_2 = 2$ is not, and $G(6) = \max(1, 2, 2) = 2$. -/
@[category test, AMS 11]
theorem maximal_prime_gap_initial_indices :
    IsMaximalPrimeGapIndex 0 ∧ IsMaximalPrimeGapIndex 1 ∧ ¬ IsMaximalPrimeGapIndex 2 ∧
      sup_primeGap 6 = 2 := by
  have hp0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have hp1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  have hp2 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  have hp3 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
  have hg0 : primeGap 0 = 1 := by simp [primeGap, hp0, hp1]
  have hg1 : primeGap 1 = 2 := by simp [primeGap, hp1, hp2]
  have hg2 : primeGap 2 = 2 := by simp [primeGap, hp2, hp3]
  refine ⟨fun _ hm => by omega, ?_, ?_, ?_⟩
  · intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    omega
  · intro h2
    have hlt := h2 1 (by omega)
    omega
  · unfold sup_primeGap
    have hc : ⌈(6 : ℝ)⌉₊ = 6 := by norm_num
    have hpc : Nat.primeCounting' 6 = 3 := by decide
    rw [hc, hpc]
    simp [Finset.range_add_one, hg0, hg1, hg2]

/-- Index $0$ ($g_0 = 3 - 2 = 1$) is vacuously a record prime gap index. -/
@[category API, AMS 11]
theorem isMaximalPrimeGapIndex_zero : IsMaximalPrimeGapIndex 0 :=
  maximal_prime_gap_initial_indices.1

/-- Infinitely many indices $n$ achieve a new record prime gap, since prime gaps are unbounded. -/
@[category textbook, AMS 11]
theorem infinite_maximalPrimeGapIndex :
    {n : ℕ | IsMaximalPrimeGapIndex n}.Infinite := by
  sorry

/-- Shanks's maximal prime gap conjecture (1964): the maximal prime gap $G(x)$ starting below $x$
satisfies $G(x) \sim (\log x)^2$ as $x \to \infty$ (contradicted by Granville's refinement
predicting $\limsup_{n \to \infty} g_n / (\log p_n)^2 \ge 2e^{-\gamma}$). -/
@[category research open, AMS 11]
theorem shanks_maximal_prime_gap_conjecture :
    (fun x : ℝ => (sup_primeGap x : ℝ)) ~[Filter.atTop]
      (fun x : ℝ => (Real.log x) ^ 2) := by
  sorry

/-- Record-index consequence of Shanks's conjecture (derived as a corollary of
`shanks_maximal_prime_gap_conjecture` rather than stated directly on Wikipedia): as $n$ runs
through indices with `IsMaximalPrimeGapIndex n`, the ratio $g_n / (\log p_n)^2$ converges to
$1$. -/
@[category research open, AMS 11]
theorem shanks_maximal_prime_gap_conjecture.variants.record_indices :
    Filter.Tendsto
      (fun k : {n : ℕ // IsMaximalPrimeGapIndex n} =>
        (primeGap k.1 : ℝ) / (Real.log (Nat.nth Nat.Prime k.1 : ℝ)) ^ 2)
      Filter.atTop (nhds 1) := by
  sorry

end MaximalPrimeGap
