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
# Nonexistence of optimal propositional proof systems

*References:*
* Krajíček, *The Cook-Reckhow definition* (2019), Definitions 1.1 and 2.1,
  Problem 2.3 and its five scenarios, pp. 7–8, https://arxiv.org/abs/1909.03691.
-/

namespace Arxiv.«1909.03691»

open PropositionalProof

/-- **No optimal proof system** (Krajíček, Problem 2.3): no Cook–Reckhow system
simulates every other such system. Systems are total polynomial-time maps from
binary proofs onto exactly the tautologies of the negation/implication language.
Simulation requires one translator preserving conclusions and a polynomial bound
on translated proof length; neither computability nor a time bound is required of
the translator. Bounds may depend on the two systems, not individual proofs.
This nonexistence conjecture implies $NP\ne coNP$. -/
@[category research open, AMS 3 68]
theorem no_optimal_proof_system :
    ¬ ∃ f : CookReckhow, f.Optimal := by
  sorry

/-- **No p-optimal proof system** (Krajíček, Problem 2.3): no Cook–Reckhow system
p-simulates every other such system for the same tautologies. For each source
system, p-simulation requires one deterministic polynomial-time translator on
binary proofs, preserving the conclusion and obeying a global polynomial output-
length bound. The target system is fixed before the source systems. This is the
nonexistence conjecture, not the weaker claim about a particular fixed calculus. -/
@[category research open, AMS 3 68]
theorem no_poptimal_proof_system :
    ¬ ∃ f : CookReckhow, f.POptimal := by
  sorry

end Arxiv.«1909.03691»
