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
import FormalConjecturesUtil

/-!
# Conjectures in Complexity Theory

This file contains formal statements of some of the main open conjectures
in complexity theory, including

- the P vs NP problem
- the NP vs coNP problem

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/P_versus_NP_problem)
- Arora, Sanjeev, and Boaz Barak. Computational complexity: a modern approach.
  Cambridge University Press, 2009.
- [The Clay Institute](https://www.claymath.org/millennium/p-vs-np/)
-/

open Computability Turing

namespace ComplexityTheory

/-- Sanity check: the identity function is polynomial-time computable. -/
@[category test, AMS 68]
theorem isPolyTime_id {α : Type} [BitstringEncoding α] : IsPolyTime (id : α → α) :=
  ⟨Turing.idComputableInPolyTime (BitstringEncoding.toFinEncoding α)⟩

/--
The class P is the set of decision problems
decidable in polynomial time by a deterministic Turing machine.
-/
def P : ComplexityClass :=
  { L | IsPolyTime L }

/--
The class NP is the set of decision problems
such that there exists a polynomial `p` over ℕ and a poly-time Turing machine
where for all `x`, `L x = true` iff there exists a `w` of length at most `p (|x|)`
such that the Turing machine accepts the pair `(x,w)`.

See Definition 2.1 in Arora-Barak (2009).
-/
def NP : ComplexityClass :=
  { L | ∃ (p : Polynomial ℕ), ∃ R : (List Bool × List Bool) → Bool,
      IsPolyTime R ∧
      ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ R (x, w) }

/--
The class coNP is the set of decision problems
whose complements are in NP.
-/
def coNP : ComplexityClass :=
  { L | Lᶜ ∈ NP }

/--
**P ≠ NP**:

The conjecture that the complexity classes P and NP are not equal.
-/
@[category research open, AMS 68]
theorem P_ne_NP : P ≠ NP := by sorry

/--
**NP ≠ coNP**:

The conjecture that the complexity classes NP and coNP are not equal.
-/
@[category research open, AMS 68]
theorem NP_ne_coNP : NP ≠ coNP := by sorry

/--
The theorem that the set of complements of languages in P is itself P.

This can be proven by observing that the boolean negation function is computable in polynomial time,
and that compositions of poly-time computable functions are also poly-time computable.
-/
@[category textbook, AMS 68]
theorem coP_eq_P :
    { L | Lᶜ ∈ P } = P := by
  sorry

/--
The theorem that P is a subset of NP.

This can be proven by observing that for any language in P,
we can construct a verifier that ignores the witness and simply runs the poly-time decider for the
language.
-/
@[category textbook, AMS 68]
theorem P_subset_NP :
    P ⊆ NP := by
  sorry

/--
The theorem that P is a subset of coNP.
-/
@[category textbook, AMS 68]
theorem P_subset_coNP :
    P ⊆ coNP := by
  rw [coNP, ← coP_eq_P]
  simp only [Set.setOf_subset_setOf]
  intros L hL
  exact P_subset_NP hL

end ComplexityTheory
