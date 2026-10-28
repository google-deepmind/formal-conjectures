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
# Polynomial-time computability of the discrete logarithm

This file formalizes the open problem of whether the discrete logarithm problem
in the multiplicative group of integers modulo a prime can be computed in
polynomial time on a deterministic classical Turing machine.

*References:*
- [Wikipedia: Discrete logarithm](https://en.wikipedia.org/wiki/Discrete_logarithm)
- [Wikipedia: List of unsolved problems in computer science](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_computer_science)
-/

@[expose] public section

namespace PolyTime

open ComplexityTheory Classical

/--
The decision version of the discrete logarithm problem in `(ℤ/pℤ)ˣ`:
Given `(g, h, p, k)`, where `p` is prime and `g, h` are nonzero residues modulo `p`,
does there exist `x ≤ k` such that `g^x ≡ h (mod p)`?

For inputs outside the intended group domain (`p` not prime or `g, h` not in `(0, p)`),
the decision problem evaluates to `false`.
-/
noncomputable def discreteLogDecision (input : ℕ × ℕ × ℕ × ℕ) : Bool :=
  let (g, h, p, k) := input
  if Nat.Prime p ∧ 0 < g ∧ g < p ∧ 0 < h ∧ h < p ∧ ∃ x ≤ k, (g ^ x) % p = h then
    true
  else
    false

/--
**The discrete logarithm problem is not in P**:

The conjecture that the discrete logarithm problem cannot be solved in
polynomial time on a deterministic classical computer.
-/
@[category research open, question, AMS 68]
theorem discrete_logarithm_not_in_P :
    ¬ IsPolyTime discreteLogDecision := by
  sorry

end PolyTime
