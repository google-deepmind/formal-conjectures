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

*References:*
* Allender, Farach-Colton and Tsai, *Syntactic Separation of Subset Satisfiability
  Problems*, APPROX/RANDOM 2019, Conjecture 1, p. 16:2,
  https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2019.16.
-/

namespace AllenderFarachColtonTsai2019

open Computability.GapSatisfiability

/-- **Deterministic Gap-ETH** (Conjecture 1): some rational $0<\varepsilon<1$ and
integer $b>0$ exclude time $C(L+1)^k2^{\lfloor n/b\rfloor}$ separation of satisfiable
3-CNF formulas from those where every assignment leaves at least an $\varepsilon$
fraction of clauses unsatisfied, for any fixed $C,k$. Input is a nonempty binary
formula of length $L$ with $n$ distinct occurring variables and at most three
literals per clause. Repeated clause positions count separately; empty clauses
are unsatisfied. One deterministic TM2 must meet the clock on both promises, with
no requirement outside them. This hypothesis implies $P\ne NP$. -/
@[category research open, AMS 68]
theorem gap_ETH :
    ∃ ε : ℚ, 0 < ε ∧ ε < 1 ∧
      ∃ b : ℕ, 0 < b ∧ ¬ HasExponentialSeparator ε b := by sorry

end AllenderFarachColtonTsai2019
