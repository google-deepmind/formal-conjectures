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
# Erdős Problem 382

*References:*
- [erdosproblems.com/382](https://www.erdosproblems.com/382)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
-/

@[expose] public section

open Filter

namespace Erdos382

/-- `LargestPrimeRepeated u v` means that $1 \leq u \leq v$ and the largest prime $p$ dividing
$\prod_{u \leq m \leq v} m$ appears in it with exponent at least $2$, that is $p^2$ divides the
product.

We require $u \geq 1$, since for $u = 0$ the product is $0$ and `Nat.maxPrimeFac 0 = 0`. We also
require $v \geq 2$: the only other pair is $u = v = 1$, where the product is $1$, which has no
prime factor, and the junk value `Nat.maxPrimeFac 1 = 1` would make the condition hold. -/
def LargestPrimeRepeated (u v : ℕ) : Prop :=
  1 ≤ u ∧ u ≤ v ∧ 2 ≤ v ∧
    Nat.maxPrimeFac (∏ m ∈ Finset.Icc u v, m) ^ 2 ∣ ∏ m ∈ Finset.Icc u v, m

/-- The pair $(48, 50)$ satisfies the condition: $48 \cdot 49 \cdot 50 = 2^5 \cdot 3 \cdot 5^2
\cdot 7^2$, and the largest prime $7$ appears with exponent $2$. -/
@[category test, AMS 11]
theorem largestPrimeRepeated_48_50 : LargestPrimeRepeated 48 50 := by
  sorry

/-- If the condition holds, then $v < 2u$.

Otherwise $2u \leq v$, and by Bertrand's postulate there is a prime $q$ with $v/2 < q \leq v$, so
$u \leq q \leq v$. The largest prime $p$ of the product satisfies $p \geq q > v/2$. Hence $p$
divides exactly one factor $m \in [u, v]$, namely $m = p$, and $p$ appears with exponent $1$. -/
@[category textbook, AMS 11]
theorem lt_two_mul_of_largestPrimeRepeated {u v : ℕ} (h : LargestPrimeRepeated u v) :
    v < 2 * u := by
  sorry

/--
Let $u \leq v$ be such that the largest prime dividing $\prod_{u \leq m \leq v} m$ appears with
exponent at least $2$. Is it true that $v - u = v^{o(1)}$?

We read this as: for every $\epsilon > 0$, every such pair with $v$ large enough satisfies
$v - u \leq v^{\epsilon}$. Cambie observed that this question reduces to old conjectures on gaps
between primes; for example, it follows from Cramér's conjecture. See also Erdős Problems 380 and
383.
-/
@[category research open, AMS 11]
theorem erdos_382.parts.i : answer(sorry) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ v : ℕ in atTop, ∀ u : ℕ, LargestPrimeRepeated u v →
      ((v - u : ℕ) : ℝ) ≤ (v : ℝ) ^ ε := by
  sorry

/--
Let $u \leq v$ be such that the largest prime dividing $\prod_{u \leq m \leq v} m$ appears with
exponent at least $2$. Can $v - u$ be arbitrarily large?

That is, for every $k$, is there such a pair with $v - u \geq k$? Cambie gives a heuristic that
suggests the answer is yes.
-/
@[category research open, AMS 11]
theorem erdos_382.parts.ii : answer(sorry) ↔
    ∀ k : ℕ, ∃ u v : ℕ, LargestPrimeRepeated u v ∧ k ≤ v - u := by
  sorry

/--
Erdős and Graham [ErGr80] report that it follows from results of Ramachandra that
$v - u \leq v^{1/2+o(1)}$ for every pair $u \leq v$ as in `Erdos382.erdos_382.parts.i`.

That is, for every $\epsilon > 0$, every such pair with $v$ large enough satisfies
$v - u \leq v^{1/2+\epsilon}$.
-/
@[category research solved, AMS 11]
theorem erdos_382.variants.ramachandra :
    ∀ ε > (0 : ℝ), ∀ᶠ v : ℕ in atTop, ∀ u : ℕ, LargestPrimeRepeated u v →
      ((v - u : ℕ) : ℝ) ≤ (v : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  sorry

end Erdos382
