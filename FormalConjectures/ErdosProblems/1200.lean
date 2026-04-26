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
# Erdős Problem 1200
*Reference:*
- [erdosproblems.com/1200](https://www.erdosproblems.com/1200)
- [erdosproblems.com/688](https://www.erdosproblems.com/688)
- [ErRu80] Erdős, P. and Ruzsa, I. Z., _On the small sieve. I. Sifting by primes_. J. Number Theory (1980), 385--394.
-/

open Classical

namespace Erdos1200

/--
There exists a constant $C$ such that for all large $x$ there is a collection of primes
$p_1 < \dots < p_k < x$ with $\sum \frac{1}{p_i} < C$ together with a system of congruences
$a_i \pmod{p_i}$ such that every integer $n < x$ satisfies at least one of these congruences.
-/

@[category research open, AMS 11]
theorem erdos_1200 :
  ∃ (C : ℝ), (C > 0) ∧ ∀ᶠ (x : ℝ) in Filter.atTop,
      ∃ (S : Finset ℕ), ∃ (a : ℕ → ℕ),
        (∀ p ∈ S, Nat.Prime p) ∧
        (∀ p ∈ S, p < x) ∧
        (∑ p ∈ S, (1 : ℝ) / p < C) ∧
        (∀ (n : ℕ), (1 ≤ n) ∧ (n < x) → ∃ p ∈ S, a p ≡ n [MOD p])
  := by sorry

/--
A variant of [erdosproblems.com/688] which implies [erdosproblems.com/1200].
-/

def prop_of_erdos_688 (n : ℕ) (ε : ℝ) : Prop :=
  ∃ (a : ℕ → ℕ), ∀ (m : ℕ), (1 ≤ m) ∧ (m ≤ n) →
    ∃ (p : ℕ), (Nat.Prime p) ∧ ((n : ℝ)^ε < p) ∧ (p ≤ n) ∧
    (a p ≡ m [MOD p])

noncomputable def epsilon_function (n : ℕ) : ℝ := sSup {ε : ℝ | prop_of_erdos_688 n ε}

@[category research open, AMS 11]
theorem erdos_1200.variants.modified_erdos_688 :
  (fun (n : ℕ) ↦ (1 : ℝ)) =O[Filter.atTop] epsilon_function
  := by sorry

/--
In [ErRu80] this is asked as a question: if $p_1 < \dots < p_k < x$ are primes with
$\sum \frac{1}{p_i} \leq C$ and $a_i \pmod {p_i}$ are any residue classes then
must there always be $\gg_C x$ many integers $n < x$ avoiding all of them?

Of course if the answer is yes then this disproves [erdosproblems.com/1200].
-/

def avoids_congruences (S : Finset ℕ) (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ p ∈ S, ¬(a p ≡ n [MOD p])

@[category research open, AMS 11]
theorem erdos_1200.variants.ErRu80_question : answer(sorry) ↔
  ∀ (C : ℝ), (C > 0) → ∃ (c : ℝ), (c > 0) ∧
    ∀ (x : ℝ), (x > 0) → ∀ (S : Finset ℕ), ∀ (a : ℕ → ℕ),
      (∀ p ∈ S, Nat.Prime p) ∧
      (∀ p ∈ S, p < x) ∧
      (∑ p ∈ S, (1 : ℝ) / p ≤ C) → Finset.card (Finset.filter
        (fun (m : ℕ) ↦ avoids_congruences S a m)
        (Finset.Icc (1 : ℕ) (Int.floor x).toNat))
      ≥ c * x
  := by sorry

/--
Erdős and Ruzsa [ErRu80] proved that for any $C > 0$ there exists a set of primes $P$
such that $\sum_{p ∈ P} \frac{1}{p} \leq C$ and the number of integers $n \leq x$ divisible
by at least one $p \in P$ is $\gg_C x$.
-/

@[category research solved, AMS 11]
theorem erdos_1200.variants.ErRu80_theorem :
  ∀ (C : ℝ), (C > 0) → ∃ (c : ℝ), (c > 0) ∧ ∃ (P : Set ℕ),
    (∀ p ∈ P, Nat.Prime p) ∧
    (∑' p : ℕ, Set.indicator P (fun (k : ℕ) ↦ (1 : ℝ) / k) p > 0) ∧
    (∑' p : ℕ, Set.indicator P (fun (k : ℕ) ↦ (1 : ℝ) / k) p ≤ C) ∧
    ∀ (x : ℝ), (x > 0) → Finset.card (Finset.filter
      (fun (m : ℕ) ↦ ∃ p ∈ P, p ∣ m)
      (Finset.Icc (1 : ℕ) (Int.floor x).toNat))
    ≥ c * x
  := by sorry

end Erdos1200
