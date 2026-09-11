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
* Manurangsi and Raghavendra, *A Birthday Repetition Theorem and Complexity of
  Approximating Dense CSPs*, arXiv:1607.02986, §2.6, Conjecture 2, p. 11,
  https://arxiv.org/abs/1607.02986.
* Irit Dinur, *Mildly exponential reduction from gap 3SAT to polynomial-gap
  label-cover*, ECCC TR16-128, §2.2, Hypothesis 2.5, pp. 5–6,
  https://eccc.weizmann.ac.il/report/2016/128/.
* Allender, Farach-Colton and Tsai, *Syntactic Separation of Subset Satisfiability
  Problems*, APPROX/RANDOM 2019, Conjecture 1, p. 16:2,
  https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2019.16.
-/

namespace Arxiv.«1607.02986»

open Computability.GapSatisfiability

/-- **Deterministic Gap-ETH**, introduced by Dinur and independently by Manurangsi
and Raghavendra, in the variable-count form of Allender et al., Conjecture 1:
some rational $0<\varepsilon<1$ and
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

end Arxiv.«1607.02986»
