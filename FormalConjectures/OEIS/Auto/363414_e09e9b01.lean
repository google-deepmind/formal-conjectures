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

open Nat Finset Complex Real

/--
A363414: $a(n) = (1/2) \cdot \operatorname{Im}\left( \prod_{k = 0}^{n} (1 + k\sqrt{-4}) \right)$.
The sequence values are integers.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let P_n : Complex :=
    Finset.prod (range (n + 1))
    (fun k : ℕ ↦ (1 : Complex) + ((2 * k : ℕ) : ℝ) * Complex.I)

  Int.floor (P_n.im / 2)

open Filter Asymptotics ZMod Int

/--
The set of primes of type 2 for A363414 is conjecturally
$\mathbb{P}_2 = \{p \mid p \equiv 1 \pmod 4\}$.
-/
def type_two_primes_conjectured : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ (p : ZMod 4) = 1}

/--
Conjecture A363414: Type 1 primes set is empty.
It appears that every prime p divides some term of the sequence.
The claim formalizes: every prime $p$ divides some $a(n)$.
-/
theorem oeis_363414_conjecture_type1_empty :
  ∀ p : ℕ, Nat.Prime p → ∃ n : ℕ, (p : ℤ) ∣ a n := by sorry

/--
Moll's conjecture 5.5 extends to this sequence:
for the primes of type 2, the p-adic valuation $\nu_p(a(n)) \sim n/(p - 1)$ as $n \to \infty$.
This is formalized using asymptotic equivalence (`~[atTop]`) for the p-adic valuation
(`padicValInt`) converted to a real number.
-/
theorem oeis_363414_conjecture_type2_asymptotics :
  ∀ p : ℕ, Nat.Prime p → p ∈ type_two_primes_conjectured →
  (fun n ↦ (padicValInt p (a n) : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) / ((p : ℝ) - 1)) := by sorry
