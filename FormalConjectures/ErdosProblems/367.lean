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
# Erdős Problem 367

*References:*
- [erdosproblems.com/367](https://www.erdosproblems.com/367)
- [ErGr80] P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, L'Enseignement Mathématique (1980).
-/

open Asymptotics Filter

namespace Erdos367

/--
`B r n` is the $r$-full part of $n$: the product of prime powers $p^a \| n$ with $a \geq r$.
-/
def B (r n : ℕ) : ℕ :=
  ∏ i ∈ n.factorization.support with r ≤ n.factorization i, i ^ n.factorization i

/--
Let $B_2(n)$ be the $2$-full part of $n$ (that is, $B_2(n)=n/n'$ where $n'$ is the product of all
primes that divide $n$ exactly once). Is it true that, for every fixed $k \geq 1$,
$\prod_{n \leq m < n+k} B_2(m) \ll n^{2+o(1)}$?
-/
@[category research open, AMS 11]
theorem erdos_367.parts.i : answer(sorry) ↔ ∀ k : ℕ, 1 ≤ k →
    ∃ e : ℕ → ℝ,
      e =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n in atTop,
        ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ) ≤ (n : ℝ) ^ (2 + e n) := by
  sorry

/--
Or perhaps even $\prod_{n \leq m < n+k} B_2(m) \ll_k n^2$?

van Doorn notes in the comments that this fails for all $k \geq 3$.
-/
@[category research solved, AMS 11]
theorem erdos_367.parts.ii : answer(False) ↔ ∀ k : ℕ, 1 ≤ k →
    (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  sorry

/--
van Doorn notes in the comments that for $k \leq 2$ we trivially have
$\prod_{n \leq m < n+k} B_2(m) \ll n^2$.
-/
@[category research solved, AMS 11]
theorem erdos_367.variants.k_le_two : ∀ k : ℕ, k ≤ 2 →
    (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  sorry

/--
But this fails for all $k \geq 3$, and in fact
$\prod_{n \leq m < n+3} B_2(m) \gg n^2 \log n$ infinitely often.
-/
@[category research solved, AMS 11]
theorem erdos_367.variants.k_ge_three_lower :
    ∃ c > (0 : ℝ), ∃ᶠ (n : ℕ) in atTop,
      c * ((n : ℝ) ^ 2 * Real.log (n : ℝ)) ≤
        ((∏ m ∈ .Ico n (n + 3), B 2 m : ℕ) : ℝ) := by
  sorry

/--
It would also be interesting to find upper and lower bounds for the analogous product with $B_r$
for $r \geq 3$, where $B_r(n)$ is the $r$-full part of $n$ (that is, the product of prime powers
$p^a \mid n$ such that $p^{a+1} \nmid n$ and $a \geq r$). Is it true that, for every fixed
$r,k \geq 2$ and $\epsilon > 0$,
$\limsup \frac{\prod_{n \leq m < n+k} B_r(m)}{n^{1+\epsilon}} \to \infty$?
-/
@[category research open, AMS 11]
theorem erdos_367.variants.higher_full_parts : answer(sorry) ↔
    ∀ r k : ℕ, 3 ≤ r → 2 ≤ k → ∀ ε : ℝ, 0 < ε →
      atTop.limsup (fun n ↦
        ((∏ m ∈ .Ico n (n + k), B r m : ℕ) / (n : ℝ) ^ (1 + ε) |>.toEReal)) = ⊤ := by
  sorry

end Erdos367
