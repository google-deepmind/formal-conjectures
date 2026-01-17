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

import FormalConjectures.Util.ProblemImports

/-!
# Ben Green's Open Problem 67

Bounds for Waring's problem over finite fields.

*Reference:* [Ben Green's Open Problem 67](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8 Problem 67)
-/

open Finset

namespace Green67

/--
For a prime $p$ and exponent $k$, `g(k, p)` is the smallest $s$ such that every element of
$\mathbb{F}_p$ can be written as the sum of at most $s$ $k$-th powers.
-/
noncomputable def waringFiniteField (k p : ℕ) [Fact p.Prime] : ℕ :=
  sInf {s : ℕ | ∀ x : ZMod p, ∃ (f : Fin s → ZMod p), x = ∑ i, (f i) ^ k}

/--
What is the order of magnitude of $g(k, p)$ for fixed $k$ as $p \to \infty$?

The problem asks for bounds on the Waring function over finite fields.
-/
@[category research open, AMS 11]
theorem green_67 (k : ℕ) (hk : k ≥ 2) :
    (fun p : ℕ => (waringFiniteField k p : ℝ)) =Θ[Filter.atTop.comap Nat.Prime]
      (answer(sorry) : ℕ → ℝ) := by
  sorry

end Green67
