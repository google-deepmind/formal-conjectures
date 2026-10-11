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
# Explicit Boolean circuit lower bounds

These conjectures ask for families whose truth tables can be printed in time polynomial
in $2^n$ and which eventually require the specified number of $B_2$ gates. All logarithms
are base two. Each gate computes one of the sixteen binary Boolean operations.

The numerical bounds are milestones toward explicit hardness at the Shannon–Lupanov scale.
Jukna supplies the circuit model and this scale; the explicitness and eventual lower-bound
conventions here differ from his $\mathsf{NP}$ and infinitely-often conventions.

*Reference:* Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*,
Springer, 2012, Sections 1.2, 1.4.1, and 1.5.1 of
[Chapter 1](https://web.vu.lt/mif/s.jukna/boolean/chapter1.pdf).
-/

@[expose] public section

namespace ComplexityTheory

local notation "log₂" => Real.logb 2

/-- There is an explicit Boolean family requiring at least $5n$ gates for all sufficiently
large $n$. -/
@[category research open, AMS 68]
theorem exists_explicit_five_mul :
    ∃ f, Explicit f ∧ CircuitLowerBound f (fun n => 5 * n) := by
  sorry

/-- There is an explicit Boolean family requiring at least $50n$ gates for all sufficiently
large $n$. -/
@[category research open, AMS 68]
theorem exists_explicit_fifty_mul :
    ∃ f, Explicit f ∧ CircuitLowerBound f (fun n => 50 * n) := by
  sorry

/-- There is an explicit Boolean family requiring at least $n\log_2 n$ gates for all
sufficiently large $n$. -/
@[category research open, AMS 68]
theorem exists_explicit_n_log_n :
    ∃ f, Explicit f ∧ CircuitLowerBound f (fun n => n * log₂ n) := by
  sorry

/-- There is an explicit Boolean family requiring at least
$n\log_2 n\,(\log_2 n)^{\log_2\log_2 n}$ gates for all sufficiently large $n$. -/
@[category research open, AMS 68]
theorem exists_explicit_n_log_n_log_power :
    ∃ f, Explicit f ∧ CircuitLowerBound f
      (fun n => n * log₂ n * (log₂ n) ^ (log₂ (log₂ n))) := by
  sorry

/-- For each fixed $k\ge 2$, there is an explicit Boolean family requiring at least $n^k$
gates for all sufficiently large $n$. The family may depend on $k$. -/
@[category research open, AMS 68]
theorem exists_explicit_polynomial :
    ∀ k : ℕ, 2 ≤ k → ∃ f, Explicit f ∧ CircuitLowerBound f (fun n => (n : ℝ) ^ k) := by
  sorry

/-- There is one explicit Boolean family which, for every fixed $k$, requires at least $n^k$
gates for all sufficiently large $n$. The threshold may depend on $k$. -/
@[category research open, AMS 68]
theorem exists_explicit_superpolynomial :
    ∃ f, Explicit f ∧ ∀ k : ℕ, CircuitLowerBound f (fun n => (n : ℝ) ^ k) := by
  sorry

/-- There is an explicit Boolean family requiring at least $2^{n/2}$ gates for all
sufficiently large $n$. -/
@[category research open, AMS 68]
theorem exists_explicit_two_pow_half :
    ∃ f, Explicit f ∧ CircuitLowerBound f (fun n => (2 : ℝ) ^ ((n : ℝ) / 2)) := by
  sorry

/-- There is an explicit Boolean family requiring at least $(1-\varepsilon)2^n/n$ gates
for all sufficiently large $n$, with the fixed choice $\varepsilon=1/2$. -/
@[category research open, AMS 68]
theorem exists_explicit_half_maximum :
    ∃ f, Explicit f ∧ CircuitLowerBound f (fun n => (1 / 2 : ℝ) * 2 ^ n / n) := by
  sorry

/-- There is one explicit Boolean family which, for every $0<\varepsilon<1$, requires at
least $(1-\varepsilon)2^n/n$ gates for all sufficiently large $n$. The threshold may depend
on $\varepsilon$. -/
@[category research open, AMS 68]
theorem exists_explicit_near_maximum :
    ∃ f, Explicit f ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      CircuitLowerBound f (fun n => (1 - ε) * 2 ^ n / n) := by
  sorry

end ComplexityTheory
