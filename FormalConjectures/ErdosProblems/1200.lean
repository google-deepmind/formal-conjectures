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
# Erdős Problem 1200

*References:*
- [erdosproblems.com/1200](https://www.erdosproblems.com/1200)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [ErRu80] Erdős, P. and Ruzsa, I. Z., *On the small sieve. I. Sifting by primes*. J. Number
  Theory (1980), 385--394.
-/

@[expose] public section

open Filter

namespace Erdos1200

/--
There exists a constant $C$ such that for all large $x$ there is a collection of primes
$p_1<\cdots<p_k<x$ with $\sum\frac{1}{p_i}<C$ together with a system of congruences
$a_i\pmod{p_i}$ such that every integer $1 \leq n<x$ satisfies at least one of these congruences.

A conjecture of Erdős and Ruzsa, which Erdős described in [Er80] as 'surprising'.

It suffices to consider integer $x$, since for real $x$ the primes $p < x$ and the integers
$n < x$ are the same as those below $\lceil x \rceil$.
-/
@[category research open, AMS 11]
theorem erdos_1200 :
    ∃ C : ℝ, ∀ᶠ x : ℕ in atTop, ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p < x) ∧
      ∑ p ∈ P, (1 : ℝ) / p < C ∧
      ∃ a : ℕ → ℕ, ∀ n, 1 ≤ n → n < x → ∃ p ∈ P, n ≡ a p [MOD p] := by
  sorry

/--
In [ErRu80] the question is asked in the opposite direction: if $p_1<\cdots<p_k<x$ are primes
with $\sum\frac{1}{p_i}\leq C$ and $a_i\pmod{p_i}$ are any residue classes, must there always be
$\gg_C x$ many integers $1 \leq n<x$ avoiding all of them? A positive answer disproves
`erdos_1200`.
-/
@[category research open, question, AMS 11]
theorem erdos_1200.variants.small_sieve :
    ∀ C : ℝ, ∃ c > (0 : ℝ), ∀ᶠ x : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p < x) →
      ∑ p ∈ P, (1 : ℝ) / p ≤ C → ∀ a : ℕ → ℕ,
        c * x ≤ ((Finset.Ico 1 x).filter fun n ↦ ∀ p ∈ P, ¬ n ≡ a p [MOD p]).card := by
  sorry

end Erdos1200
