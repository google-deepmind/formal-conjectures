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
# Erdős Problem 685

*References:*
- [erdosproblems.com/685](https://www.erdosproblems.com/685)
- [Er79d] Erdős, P., *Some unconventional problems in number theory*. Acta Math. Acad. Sci.
  Hungar. (1979), 71-80.
-/

@[expose] public section

open Filter
open scoped ArithmeticFunction.omega

namespace Erdos685

/-- `primeRecipSum k n` is the sum of $1/p$ over the primes $k < p < n$. -/
noncomputable def primeRecipSum (k n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioo k n).filter Nat.Prime, (1 : ℝ) / p

/-- Both ends are excluded: the only prime strictly between $2$ and $5$ is $3$. -/
@[category test, AMS 11]
theorem primeRecipSum_two_five : primeRecipSum 2 5 = 1 / 3 := by
  rw [primeRecipSum, show (Finset.Ioo 2 5).filter Nat.Prime = {3} by decide]
  norm_num

/--
Let $\epsilon > 0$ and let $n$ be large depending on $\epsilon$. Is it true that for all
$n^{\epsilon} < k \leq n^{1-\epsilon}$ the number of distinct prime divisors of $\binom{n}{k}$ is
$$(1+o(1))\, k \sum_{k < p < n} \frac{1}{p}?$$

The $o(1)$ is uniform in $k$.
-/
@[category research open, question, AMS 11]
theorem erdos_685.parts.i :
    ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (n : ℝ) ^ ε < (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ (1 - ε) →
        |(ω (n.choose k) : ℝ) - (k : ℝ) * primeRecipSum k n| ≤
          δ * ((k : ℝ) * primeRecipSum k n) := by
  sorry

/--
Is it true that, for some constant $c > 0$, the number of distinct prime divisors of
$\binom{n}{k}$ is
$$(1+o(1))\, k \sum_{k < p < n} \frac{1}{p}$$
even for all $(\log n)^c \leq k \leq n^{1-\epsilon}$?

Here $\epsilon > 0$ is as in the first question, and the $o(1)$ is uniform in $k$.
-/
@[category research open, question, AMS 11]
theorem erdos_685.parts.ii :
    ∃ c > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      Real.log (n : ℝ) ^ c ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ (1 - ε) →
        |(ω (n.choose k) : ℝ) - (k : ℝ) * primeRecipSum k n| ≤
          δ * ((k : ℝ) * primeRecipSum k n) := by
  sorry

/--
For $1 \leq k \leq n - 1$ the number of distinct prime divisors of $\binom{n}{k}$ satisfies
$$\omega\left(\binom{n}{k}\right) \geq \frac{\log \binom{n}{k}}{\log n}.$$
-/
@[category textbook, AMS 11]
theorem erdos_685.variants.trivial_lower_bound :
    ∀ n k : ℕ, 0 < k → k < n →
      Real.log (n.choose k : ℝ) / Real.log (n : ℝ) ≤ (ω (n.choose k) : ℝ) := by
  intro n k hk0 hkn
  have hn : 1 < n := by omega
  have hchoose : n.choose k ≤ n ^ (ω (n.choose k)) := by
    have hc : (n.choose k).primeFactors.card = ω (n.choose k) := by
      simp only [Nat.primeFactors, List.card_toFinset, ArithmeticFunction.cardDistinctFactors_apply]
    calc
      n.choose k = ∏ p ∈ (n.choose k).primeFactors,
          p ^ (n.choose k).factorization p :=
        Nat.prod_primeFactors_pow_factorization (Nat.choose_ne_zero hkn.le)
      _ ≤ ∏ _p ∈ (n.choose k).primeFactors, n :=
        Finset.prod_le_prod' fun _ _ => Nat.pow_factorization_choose_le (by omega)
      _ = n ^ (ω (n.choose k)) := by simp [hc]
  have hp : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  apply (div_le_iff₀ hp).mpr
  have hpow : (n.choose k : ℝ) ≤ (n : ℝ) ^ (ω (n.choose k)) := by
    exact_mod_cast hchoose
  have hlog := Real.log_le_log (Nat.cast_pos.mpr (Nat.choose_pos hkn.le)) hpow
  simpa only [Real.log_pow] using hlog

end Erdos685
