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

import FormalConjectures.Util.ProblemImports

/-!
# Green's Open Problem 27

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.27)
- [Be23] Bedert, Benjamin. "On unique sums in Abelian groups." Combinatorica 44.2 (2024): 269-298.
- [St76] Straus, E. G. "Differences of residues (mod p)." Journal of Number Theory 8.1 (1976): 40-42.
-/

open Asymptotics Filter

namespace Green27
/--
A set `A` has no unique representation in its sumset `A + A` if for every pair of elements
`a₁, a₂ ∈ A`, there exist another pair of elements `b₁, b₂ ∈ A` such that `a₁ + a₂ = b₁ + b₂`
and `{a₁, a₂} ≠ {b₁, b₂}`.
-/
def HasNoUniqueRepresentation {G : Type*} [AddCommMonoid G] (A : Finset G) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∃ b₁ ∈ A, ∃ b₂ ∈ A,
    a₁ + a₂ = b₁ + b₂ ∧ ¬((a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁))

/--
This is $m(p)$ in [Be23]: the size of the smallest set $A \subset \mathbb{Z} / p\mathbb{Z}$ (with
at least two elements) for which no element in the sumset $A + A$ has a unique representation.
-/
noncomputable def m (p : ℕ) : ℝ :=
  (sInf { (A.card) | (A : Finset (ZMod p)) (_ : 2 ≤ A.card) (_ : HasNoUniqueRepresentation A) } : ℝ)

/-- `atTop` restricted to prime numbers. -/
def primesAtTop : Filter ℕ := atTop ⊓ 𝓟 {p : ℕ | p.Prime}

/-- Best-known lower bound [Be23, Theorem 3]. -/
noncomputable def lowerBest (p : ℕ) : ℝ :=
  (Real.sqrt (Real.log (Real.log (Real.log (p : ℝ)))) /
   Real.log (Real.log (Real.log (Real.log (p : ℝ))))) * Real.log (p : ℝ)

/-- Best-known upper bound [Be23, Theorem 5]. -/
noncomputable def upperBest (p : ℕ) : ℝ := (Real.log (p : ℝ)) ^ 2

/--
What is the size of the smallest set $A \subset \mathbb{Z} / p\mathbb{Z}$ (with at least two elements)
for which no element in the sumset $A + A$ has a unique representation?
-/
@[category research open, AMS 5 11]
theorem green_27.equivalent :
  (answer(sorry) : ℕ → ℝ) ~[primesAtTop] m := by
  sorry

/-- Propose a better lower bound along primes. -/
@[category research open, AMS 5 11]
theorem green_27.lower :
    let ans := (answer(sorry) : ℕ → ℝ)
    (lowerBest =o[primesAtTop] ans) ∧ (ans =O[primesAtTop] m) := by
  sorry

/-- Propose a better upper bound along primes. -/
@[category research open, AMS 5 11]
theorem green_27.upper :
    let ans := (answer(sorry) : ℕ → ℝ)
    (ans =o[primesAtTop] upperBest) ∧ (m =O[primesAtTop] ans) := by
  sorry

/--
We have $m(p) \geq \omega(p) \log p$ for some function $\omega(p)$ tending to infinity [Be23, Theorem 3].
-/
@[category research solved, AMS 5 11]
theorem green_27.variants.lower_be23 :
  ∃ ω : ℕ → ℝ, Tendsto ω primesAtTop atTop ∧
    ∀ᶠ p in primesAtTop,
      ω p * Real.log (p : ℝ) ≤ m p := by
  sorry

/-- Upper bound: $m(p) \ll (\log p)^2$ [Be23, Theorem 5]. -/
@[category research solved, AMS 5 11]
theorem green_27.variants.upper_be23 :
  m =O[primesAtTop] upperBest := by
  sorry

/-- Previous best-known lower bound $\log p \ll m(p)$ from [St76]. -/
@[category research solved, AMS 5 11]
theorem green_27.variants.previous_lower :
  (fun p ↦ Real.log (p : ℝ)) =O[primesAtTop] m := by
  sorry

/-- Previous best-known upper bound $m(p) \ll \sqrt{p}$ from [Be23]. -/
@[category research solved, AMS 5 11]
theorem green_27.variants.previous_upper :
  m =O[primesAtTop] (fun p ↦ Real.sqrt (p : ℝ)) := by
  sorry

end Green27
