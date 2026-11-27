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
# Unconditional variants of simultaneous primitive roots

OpenAI [OAI26, Theorem 1.1] states that, under four analytic inputs, any nonempty
finite set $A$ of positive primes has the following property: for some $c_A > 0$
and all sufficiently large $x$, at least $c_A x/(\log x)^2$ primes $p \in (x, 2x)$
make every element of $A$ a primitive root modulo $p$.

A natural extension of this result is to remove the four analytic hypotheses.
A stronger extension would allow integer bases at least $2$ satisfying the square
condition and improve the lower bound to $c_A x/\log x$ in $(x, 2x]$.

*References:*
- [OAI26] OpenAI, *Simultaneous primitive roots: a conditional
lower bound for prime bases* (2026), Theorem 1.1.
https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/simultaneous-primitive-roots-conditional-lower-bound-prime-bases.pdf
- [Ki26] Kenta Kitamura, *Positive Lower Density of Simultaneous Primitive Roots*
  (2026), accompanying Lean formalization.
  https://github.com/KitaKen1/simultaneous-primitive-roots
-/

@[expose] public section

namespace SimultaneousPrimitiveRootsChallenge

/-- Unconditional variant of [OAI26, Theorem 1.1]: a $c_A x/(\log x)^2$ lower bound
for simultaneous primitive roots of any nonempty finite set of prime bases. -/
@[category research solved, AMS 11,
    formal_proof using lean4 at "https://github.com/KitaKen1/simultaneous-primitive-roots/blob/c4775966844ff78f0488492ee2aef7bd1437c51d/lean/Solution.lean"]
theorem simultaneous_primitive_roots_unconditional :
    ∀ A : Finset ℕ, A.Nonempty →
      (∀ a ∈ A, a.Prime) →
      ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        c * (x / (Real.log x) ^ 2) ≤
          (Nat.card {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ p.Prime ∧
            ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} : ℝ) := by
  sorry

/-- Stronger variant: a $c_A x/\log x$ lower bound for integer bases at least $2$
satisfying the square condition. -/
@[category research solved, AMS 11,
    formal_proof using lean4 at "https://github.com/KitaKen1/simultaneous-primitive-roots/blob/c4775966844ff78f0488492ee2aef7bd1437c51d/lean/Solution.lean"]
theorem positive_lower_density :
    ∀ A : Finset ℕ, A.Nonempty →
      (∀ a ∈ A, 2 ≤ a) →
      (∀ B : Finset ℕ, B ⊆ A → Odd B.card → ¬ IsSquare (∏ a ∈ B, a)) →
      ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        c * (x / Real.log x) ≤
          (Nat.card {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ p.Prime ∧
            ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} : ℝ) := by
  sorry

end SimultaneousPrimitiveRootsChallenge
