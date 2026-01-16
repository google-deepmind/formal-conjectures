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

import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import FormalConjectures.Util.ProblemImports
import FormalConjectures.Util.Category
import FormalConjectures.Util.AMS

/-!
# Ben Green's Open Problem 45

For each prime `p ≤ N`, choose a residue class modulo `p`.
Is it possible to make such choices so that every integer `n ≤ N`
lies in at least 10 of the chosen residue classes?

This file only sets up the basic objects needed to state the problem.
No attempt is made here to solve the conjecture.
-/

/-- A choice of one residue class modulo each prime `p ≤ N`. -/
def ResidueChoice (N : ℕ) :=
  ∀ p : ℕ, p.Prime → p ≤ N → ZMod p

/--
Given a choice of residue classes, an integer `n` satisfies the
condition for a prime `p` if it lies in the chosen residue class
modulo `p`.
-/
def LiesInClass
    {N : ℕ} (f : ResidueChoice N) (n p : ℕ)
    (hp : p.Prime) (hpn : p ≤ N) : Prop :=
  (n : ZMod p) = f p hp hpn

/--
Informal statement:

There exists a choice of residue classes modulo primes `p ≤ N`
such that every integer `n ≤ N` lies in at least 10 of them.
-/
@[category research open]
@[AMS 11] -- Number Theory
theorem GreensOpenProblem45 (N : ℕ) :
    ∃ f : ResidueChoice N,
      ∀ n ≤ N,
        10 ≤
          (Finset.filter
            (fun p =>
              p.Prime ∧ p ≤ N ∧
              LiesInClass f n p (by sorry) (by sorry))
            (Finset.range (N + 1))).card := by
  sorry


