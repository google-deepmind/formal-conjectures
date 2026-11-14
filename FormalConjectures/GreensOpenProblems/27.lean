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
public import FormalConjecturesForMathlib.Combinatorics.Basic

/-!
# Green's Open Problem 27

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.27)
- [Be23] Bedert, Benjamin. "On unique sums in Abelian groups." Combinatorica 44.2 (2024): 269-298.
- [CY26] Cao, Jiao-Long, and Ye Yuan. "A Second-Logarithm Lower Bound for Sets with No Unique
  Sums." arXiv preprint arXiv:2608.06728 (2026).
- [St76] Straus, E. G. "Differences of residues (mod p)." Journal of Number Theory 8.1 (1976): 40-42.
-/

@[expose] public section

open Asymptotics Filter

namespace Green27

/--
This is $m(p)$ in [Be23]: the size of the smallest set $A \subset \mathbb{Z} / p\mathbb{Z}$ (with
at least two elements) for which no element in the sumset $A + A$ has a unique representation.
-/
noncomputable def m (p : ℕ) : ℝ :=
  (sInf { (A.card) | (A : Finset (ZMod p)) (_ : 2 ≤ A.card) (_ : HasNoUniqueRepresentation A) } : ℝ)

/-- `atTop` restricted to prime numbers. -/
def primesAtTop : Filter ℕ := atTop ⊓ 𝓟 {p : ℕ | p.Prime}

/-- Bedert's lower bound [Be23, Theorem 3]. This was the best known bound when Green's list was
written; it has since been improved, see `green_27.lower`. -/
noncomputable def lowerBest (p : ℕ) : ℝ :=
  (Real.sqrt (Real.log (Real.log (Real.log (p : ℝ)))) /
   Real.log (Real.log (Real.log (Real.log (p : ℝ))))) * Real.log (p : ℝ)

/-- Best-known upper bound [Be23, Theorem 5]. -/
noncomputable def upperBest (p : ℕ) : ℝ := (Real.log (p : ℝ)) ^ 2

def green_27.equivalent.answer : ℕ → ℝ := sorry

/--
What is the size of the smallest set $A \subset \mathbb{Z} / p\mathbb{Z}$ (with at least two elements)
for which no element in the sumset $A + A$ has a unique representation?
-/
@[category research open, question value, AMS 5 11]
theorem green_27.equivalent :
  green_27.equivalent.answer ~[primesAtTop] m := by
  sorry

noncomputable def green_27.lower.answer : ℕ → ℝ := fun p ↦ Real.log p * Real.log (Real.log p)

/-- Propose a better lower bound along primes.

Cao and Yuan [CY26, Theorem 1.1] prove $m(p) \gg \log p \log \log p$. This beats `lowerBest`,
since $\sqrt{\log \log \log p} / \log \log \log \log p = o(\log \log p)$. The exact order of
$m(p)$ remains open. -/
@[category research solved, question value, AMS 5 11]
theorem green_27.lower :
    (lowerBest =o[primesAtTop] green_27.lower.answer) ∧ (green_27.lower.answer =O[primesAtTop] m)
      := by
  sorry

def green_27.upper.answer : ℕ → ℝ := sorry

/-- Propose a better upper bound along primes. -/
@[category research open, question value, AMS 5 11]
theorem green_27.upper :
    (green_27.upper.answer =o[primesAtTop] upperBest) ∧ (m =O[primesAtTop] green_27.upper.answer)
      := by
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
  
/-- Lower bound: $\log p \log \log p \ll m(p)$ [CY26, Theorem 1.1]. -/
@[category research solved, AMS 5 11]
theorem green_27.variants.lower_cy26 :
  (fun p ↦ Real.log (p : ℝ) * Real.log (Real.log (p : ℝ))) =O[primesAtTop] m := by
  sorry


set_option linter.style.formal_proof_palomar false in
/-- Upper bound: $m(p) \ll (\log p)^2$ [Be23, Theorem 5]. -/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/mkwatson/unique-sums-notes/blob/d4383f93a52e3a916ccce78d5fb7739c3bf3dabc/Green27Upper/Theorem.lean#L26"]
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
