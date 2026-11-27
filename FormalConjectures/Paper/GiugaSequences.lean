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
# Open problems on Giuga sequences

*Reference:* D. Borwein, J. M. Borwein, P. B. Borwein and R. Girgensohn,
*Giuga's conjecture on primality*, Amer. Math. Monthly **103** (1996), 40–50, §4 "Open problems".

A *Giuga sequence* is a finite increasing sequence of integers `n₁ < ⋯ < nₘ` with
`∑ 1/nᵢ - ∏ 1/nᵢ` a natural number. A counterexample to Giuga's conjecture (see
`FormalConjectures/Wikipedia/AgohGiuga.lean`) would have its prime factors forming a Giuga sequence
consisting of primes (a *proper* Giuga sequence).
-/

@[expose] public section

namespace GiugaSequences

/--
`S` is a Giuga sequence of value `v`: its elements are integers `> 1` and
`∑_{x ∈ S} 1/x - ∏_{x ∈ S} 1/x = v`.

Formalisation note: we require `0 < v`. With `v = 0` allowed, every singleton `{n}` would be a
Giuga sequence (`1/n - 1/n = 0`), which would make Problem 9 trivial; the sequences studied in the
reference all have positive value.
-/
def IsGiugaSequence (S : Finset ℕ) (v : ℕ) : Prop :=
  0 < v ∧ (∀ x ∈ S, 1 < x) ∧ (∑ x ∈ S, (x : ℚ)⁻¹) - (∏ x ∈ S, (x : ℚ))⁻¹ = v

@[category test, AMS 11]
theorem isGiugaSequence_2_3_5 : IsGiugaSequence {2, 3, 5} 1 := by
  refine ⟨by norm_num, by decide, ?_⟩
  norm_num

/--
Problem 3 (odd factors): find a Giuga sequence which consists of odd factors only, or prove that
none exist.

Solved: there is an odd Giuga sequence of 26 terms and value 1.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000035"]
theorem problem3_odd_factors :
    ∃ S : Finset ℕ, ∃ v, IsGiugaSequence S v ∧ ∀ x ∈ S, Odd x := by
  sorry

/--
Problem 3 (odd primes): find a Giuga sequence which consists of odd primes only, or prove that none
exist. If there were none, Giuga's conjecture would be proved.
-/
@[category research open, question, AMS 11]
theorem problem3_odd_primes :
    ∃ S : Finset ℕ, ∃ v, IsGiugaSequence S v ∧ ∀ x ∈ S, Odd x ∧ x.Prime := by
  sorry

/--
Problem 7: are there Giuga sequences with a sum-minus-product value higher than 1?
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000035"]
theorem problem7 : ∃ S : Finset ℕ, ∃ v, IsGiugaSequence S v ∧ 1 < v := by
  sorry

/--
Problem 8: are there two distinct Giuga sequences whose elements have the same product?
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000035"]
theorem problem8 :
    ∃ S T : Finset ℕ, ∃ v w, S ≠ T ∧ IsGiugaSequence S v ∧ IsGiugaSequence T w ∧
      ∏ x ∈ S, x = ∏ x ∈ T, x := by
  sorry

/--
Problem 9: can each integer be a factor in a Giuga sequence?
-/
@[category research open, question, AMS 11]
theorem problem9 :
    ∀ n, 2 ≤ n → ∃ S : Finset ℕ, ∃ v, IsGiugaSequence S v ∧ n ∈ S := by
  sorry

end GiugaSequences
