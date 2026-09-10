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
# Optimal propositional proof systems

Jan Krajíček, *The Cook-Reckhow definition* (2019), Problem 2.3, pp.7–8.
https://arxiv.org/abs/1909.03691

Simulation controls proof length; p-simulation additionally requires a
polynomial-time proof translator. The questions quantify over all Cook–Reckhow
systems for tautologies in one fixed complete propositional language.
-/

namespace Arxiv.«1909.03691»

open PropositionalProof

/-- Does an optimal propositional proof system exist?
Krajíček, Problem 2.3, asks for a system simulating every other such system. -/
@[category research open, AMS 3 68]
theorem optimal_proof_system :
    answer(sorry) ↔ ∃ f : CookReckhow, f.Optimal := by
  sorry

/-- Does a p-optimal propositional proof system exist?
This is the polynomial-time translation version of Problem 2.3. -/
@[category research open, AMS 3 68]
theorem poptimal_proof_system :
    answer(sorry) ↔ ∃ f : CookReckhow, f.POptimal := by
  sorry

end Arxiv.«1909.03691»
