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
# Deterministic Gap Exponential Time Hypothesis

Reference: Eric Allender, Martín Farach-Colton and Meng-Tsung Tsai,
*Syntactic Separation of Subset Satisfiability Problems*,
APPROX/RANDOM 2019, Conjecture 1, p.16:2:
https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2019.16.

The exponent uses the number of represented variables. A positive rate is
written as $1/b$ with positive integer b. Polynomial encoded-input overhead
is allowed. One deterministic finite TM2 machine must respect the clock and
answer correctly on both promised regions; no behavior is required elsewhere.
-/

namespace AllenderFarachColtonTsai2019

open Computability.GapSatisfiability

/-- Some fixed positive clause gap and exponential rate cannot be attained
when distinguishing satisfiable 3-CNF formulas from those in which every
assignment leaves at least that fraction of clauses unsatisfied. -/
@[category research open, AMS 68]
theorem gap_ETH :
    ∃ ε : ℚ, 0 < ε ∧ ε < 1 ∧
      ∃ b : ℕ, 0 < b ∧ ¬ HasExponentialSeparator ε b := by sorry

end AllenderFarachColtonTsai2019
