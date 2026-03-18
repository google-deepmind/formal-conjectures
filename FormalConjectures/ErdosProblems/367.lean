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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 367

*References:*
- [erdosproblems.com/367](https://www.erdosproblems.com/367)
- [ErGr80] P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, L'Enseignement Mathématique (1980).

The problem asks about bounds on products of 2-full parts over short intervals.
-/

open Asymptotics Filter

namespace Erdos367

/-- `B r n` is the $r$-full part of $n$: the product of prime powers $p^a \| n$ with $a \geq r$. -/
def B (r n : ℕ) : ℕ :=
  ∏ i ∈ n.factorization.support.filter (r ≤ n.factorization ·), i ^ n.factorization i

/--
$B_2(n) = n / n'$, where $n'$ is the product of all primes dividing $n$ exactly once,
equivalently the $2$-full part of $n$.
-/
abbrev B₂ (n : ℕ) : ℕ := B 2 n

/-- Product $\prod_{n \leq m < n+k} B_r(m)$. -/
def intervalBProduct (r n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, B r (n + i)

/-- Asymptotic formulation of an $n^{2+o(1)}$-type upper bound. -/
def nearlyQuadraticBound (k : ℕ) : Prop :=
  ∃ e : ℕ → ℝ,
    e =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n in atTop, (intervalBProduct 2 n k : ℝ) ≤ (n : ℝ) ^ (2 + e n)

/-- The stronger variant $\ll_k n^2$. -/
def quadraticBound (k : ℕ) : Prop :=
  (fun n ↦ (intervalBProduct 2 n k : ℝ)) =O[atTop] fun n ↦ (n : ℝ) ^ (2 : ℝ)

/--
Let $B_2(n)$ be the $2$-full part of $n$. Is it true that, for every fixed $k \geq 1$,
$\prod_{n \leq m < n+k} B_2(m) \ll n^{2+o(1)}$?
-/
@[category research open, AMS 11]
theorem erdos_367.parts.i : answer(sorry) ↔ ∀ k : ℕ, 1 ≤ k → nearlyQuadraticBound k := by
  sorry

/--
Or perhaps even $\prod_{n \leq m < n+k} B_2(m) \ll_k n^2$?
-/
@[category research open, AMS 11]
theorem erdos_367.parts.ii : answer(sorry) ↔ ∀ k : ℕ, 1 ≤ k → quadraticBound k := by
  sorry

/--
van Doorn notes that for $k \leq 2$ we trivially have
$\prod_{n \leq m < n+k} B_2(m) \ll n^2$.
-/
@[category research solved, AMS 11]
theorem erdos_367.variants.k_le_two : ∀ k : ℕ, k ≤ 2 → quadraticBound k := by
  sorry

/--
van Doorn also notes that the quadratic bound fails for all $k \geq 3$, and in fact
$\prod_{n \leq m < n+3} B_2(m) \gg n^2 \log n$ infinitely often.
-/
@[category research solved, AMS 11]
theorem erdos_367.variants.k_ge_three_lower :
    ∃ c > (0 : ℝ), ∀ᶠ (n : ℕ) in atTop,
      c * ((n : ℝ) ^ 2 * Real.log (n : ℝ)) ≤ (intervalBProduct 2 n 3 : ℝ) := by
  sorry

/--
Discrete limsup-unbounded formulation for the $B_r$ variant.
-/
def brRatioUnbounded (r k : ℕ) : Prop :=
  ∀ A : ℕ, ∃ n : ℕ, 1 ≤ n ∧ A * n ≤ intervalBProduct r n k

/--
It would also be interesting to find upper and lower bounds for the analogous product with $B_r$
for $r \geq 3$. Is it true that, for every fixed $r \geq 3$, $k \geq 2$, and $\epsilon > 0$,
$\limsup \frac{\prod_{n \leq m < n+k} B_r(m)}{n^{1+\epsilon}} \to \infty$?
-/
@[category research open, AMS 11]
theorem erdos_367.variants.higher_full_parts : answer(sorry) ↔
    ∀ r k : ℕ, 3 ≤ r → 2 ≤ k → brRatioUnbounded r k := by
  sorry

end Erdos367
