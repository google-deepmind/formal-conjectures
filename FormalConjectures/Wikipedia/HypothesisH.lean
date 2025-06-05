/-
Copyright 2025 The Formal Conjectures Authors.

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
# Hypothesis H

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Schinzel%27s_hypothesis_H)
-/

/--
**Bunyakovsky condition**
The condition for each polynomial in Schinzel and Bunyakovsky conjectures.
Holds for nonconstant irreducible polynomial with positive leading coefficient.
-/
def BunyakovskyCondition (f : Polynomial ℤ) : Prop :=
  1 ≤ f.degree ∧ Irreducible f ∧ 0 < f.leadingCoeff

/--
**Schinzel condition**
The collective condition on polynomials in Schinzel and Bunyakovsky conjectures.
Holds if for every prime $p$ there exists a natural $n$ such that $p$ not divides $f_i(n)$ for all $f_i$.
-/
def SchinzelCondition (fs : Finset (Polynomial ℤ)) : Prop :=
  ∀ p : ℕ, Prime p → ∃ n : ℕ, ∀ f ∈ fs, ¬(p ∣ (f.eval (n : ℤ)).natAbs)

/--
**Schinzel conjecture (H hypothesis)**
If a finite set of polynomials $f_i$ satisfies both Schinzel and Bunyakovsky conditions,
there exist infinitely many natural numbers $m$ such that $f_i(m)$ are primes for all $i$.
-/
@[category research open, AMS 11]
theorem schinzel_conjecture (fs : Finset (Polynomial ℤ)) :
  (∀ f ∈ fs, BunyakovskyCondition f) ∧ SchinzelCondition fs →
  Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime} := by
  sorry

/-! ## Special cases -/

/--
**Bunyakovsky conjecture**
If a polynomial $f$ over integers satisfies both Schinzel and Bunyakovsky conditions,
there exist infinitely many natural numbers $m$ such that $f(m)$ is prime.
-/
@[category research open, AMS 11]
theorem bunyakovsky_conjecture (f : Polynomial ℤ) :
  BunyakovskyCondition f ∧ SchinzelCondition {f} →
  Infinite {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime} := by
  sorry

/--
**Dickson's conjecture**
If a finite set of in linear integer forms $f_i(n) = a_i n+b_i$ satisfies Schinzel condition,
there exist infinitely many natural numbers $m$ such that $f_i(m)$ are primes for all $i$.
-/
@[category research open, AMS 11]
theorem dickson_conjecture (fs : Finset (Polynomial ℤ)) :
  (∀ f ∈ fs, f.degree = 1 ∧ BunyakovskyCondition f) ∧ SchinzelCondition fs →
  Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime} := by
  sorry

/--
There exist infinitely many composite Mersenne numbers.
-/
@[category research open, AMS 11]
theorem mersenne_composite_infinite :
  Infinite {n : ℕ | ¬IsGivesMersennePrime n} := by
  sorry

/--
**Polignac's conjecture**
For any integer $k$ there are infinitely many primes $p$ such that $p + 2k$ is prime.
-/
@[category research open, AMS 11]
theorem polignac_conjecture (k : ℕ) :
  Infinite {p : ℕ | Prime p ∧ Prime (p + 2*k)} := by
  sorry

/--
**Sophie Germain prime conjecture**
There are infinitely many primes $p$ such that $2p + 1$ is prime.
-/
@[category research open, AMS 11]
theorem safe_primes :
    Infinite {p : ℕ | Prime p ∧ Prime (p + 4)} := by
  sorry

/--
**Cousin primes conjecture**
There are infinitely many primes $p$ such that $p + 4$ is prime.
-/
@[category research open, AMS 11]
theorem cousin_primes :
    Infinite {p : ℕ | Prime p ∧ Prime (p + 4)} := by
  sorry

/--
**Sexy primes conjecture**
There are infinitely many primes $p$ such that $p + 6$ is prime.
-/
@[category research open, AMS 11]
theorem sexy_primes :
    Infinite {p : ℕ | Prime p ∧ Prime (p + 6)} := by
  sorry

/-
## Other special cases and consequences
- Landau's 4th problem (primes and perfect squares)
- Twin prime conjecture
-  Artin’s conjecture
-  Hardy–Littlewood conjecture
-/
