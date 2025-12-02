/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import FormalConjectures.Util.ProblemImports

open Filter Real
open Nat

namespace Erdos1004

/-- `distinct_totient_run n K` means that the values `φ(n+1), φ(n+2), ..., φ(n+K)` are all distinct. -/
def distinct_totient_run (n K : ℕ) : Prop :=
  ∀ (k₁ k₂ : ℕ) (hk₁ : k₁ < K) (hk₂ : k₂ < K),
    totient (n + k₁ + 1) = totient (n + k₂ + 1) → k₁ = k₂

/--
For any fixed c > 0, if x is sufficiently large then there exists n ≤ x such that
the values of φ(n+k) are all distinct for 1 ≤ k ≤ (log x)^c.
This is an open problem.
-/
@[category research open, AMS 11]
theorem erdos_1004 (c : ℝ) (hc : c > 0) :
    (∃ x₀ : ℕ, ∀ x ≥ x₀, ∃ n ≤ x,
      distinct_totient_run n ⌊(Real.log (x : ℝ)) ^ c⌋₊) ↔ answer(sorry) := by
  sorry

/--
Erdős, Pomerance, and Sárközy [EPS87] proved that if φ(n+k) are all distinct for 1 ≤ k ≤ K then
K ≤ n / exp(c (log n)^{1/3}) for some constant c > 0.
Here we state the existence of such a constant c.
-/
@[category research solved, AMS 11]
theorem erdos_1004.EPS87_theorem :
    (∃ (c : ℝ) (hc : c > 0),
      ∀ (n K : ℕ), distinct_totient_run n K →
        (K : ℝ) ≤ (n : ℝ) / Real.exp (c * (Real.log n) ^ (1/3 : ℝ))) ↔ answer(True) := by
  sorry

end Erdos1004
