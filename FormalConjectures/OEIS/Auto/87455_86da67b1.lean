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

open LinearRecurrence

/--
A087455: Expansion of $(1 - x)/(1 - 2 x + 3 x^2)$ in powers of $x$.
This sequence satisfies the linear recurrence relation $a(n) = 2 a(n-1) - 3 a(n-2)$ for $n \ge 2$,
with initial values $a(0)=1$ and $a(1)=1$.
The recurrence is of the form $a_{n+2} = c_0 a_n + c_1 a_{n+1}$, where $c_0 = -3$ and $c_1 = 2$.
-/
def A087455 (n : ℕ) : ℤ :=
  let order : ℕ := 2
  -- The recurrence $a_{m+2} = c_0 a_m + c_1 a_{m+1}$ where $c_0 = -3$ and $c_1 = 2$.
  -- The `Fin.cases z₀ z₁` function constructs a function from `Fin 2` by mapping 0 to $z_0$ and 1 to $k_1$.
  let coeffs : Fin order → ℤ := fun i => Fin.cases (-3) 2 i
  let E : LinearRecurrence ℤ := ⟨order, coeffs⟩
  -- Initial values: $a(0) = 1$ and $a(1) = 1$.
  let init : Fin order → ℤ := fun i => Fin.cases 1 1 i
  E.mkSol init n

/-- The proposition that the sequence of absolute values $|A087455(n)|$ satisfies Benford's law.
    This is an unproven placeholder for a complex measure theory statement not formalized in Mathlib. -/
axiom A087455_satisfies_Benfords_law : Prop

/--
A087455 It is an open question whether or not this sequence satisfies Benford's law
[Berger-Hill, 2017; Arno Berger, email, Jan 06 2017]. - N. J. A. Sloane, Feb 08 2017
-/
theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := by
  sorry
