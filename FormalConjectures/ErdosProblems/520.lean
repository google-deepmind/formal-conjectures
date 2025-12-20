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
# Erdős Problem 520

*Reference:* [erdosproblems.com/520](https://www.erdosproblems.com/520)
-/

open MeasureTheory ProbabilityTheory Nat Real Filter

section Erdos520

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/--
A Rademacher multiplicative function is a random function `f : ℕ → Ω → ℝ` satisfying:
for each prime `p`, the values `f(p)` are independent and uniformly distributed on `{-1, 1}`;
`f` is multiplicative with `f(1) = 1`; and
`f(n) = 0` whenever `n` is not squarefree.
-/
structure IsRademacherMultiplicative (f : ℕ → Ω → ℝ) : Prop where
  /-- Prime entries are independent. -/
  iIndepFun_primes : iIndepFun (fun p : Primes ↦ f p) ℙ
  /-- Primes entries are uniformly distributed on `{-1, 1}`. -/
  prob_of_prime p : p.Prime → ℙ {ω | f p ω = 1} = 1 / 2 ∧ ℙ {ω | f p ω = -1} = 1 / 2
  map_one ω : f 1 ω = 1
  map_mul_of_coprime a b ω : a.Coprime b → f (a * b) ω = f a ω * f b ω
  map_of_not_squarefree n ω : ¬ Squarefree n → f n ω = 0

/--
Is there an analogue of the law of the iterated logarithm (LIL)
for Rademacher multiplicative functions?
-/
@[category research open, AMS 11 60]
theorem erdos_520 :
    (∃ c > 0, ∀ (f : ℕ → Ω → ℝ), IsRademacherMultiplicative f →
      ∀ᵐ ω, limsup (fun N ↦ ∑ m ≤ N, f m ω / sqrt (N * log (log N))) atTop = c)
    ↔ answer(sorry) := by
  sorry

end Erdos520
