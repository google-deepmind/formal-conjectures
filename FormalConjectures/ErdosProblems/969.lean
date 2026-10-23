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
# Erdős Problem 969

*References:*
- [Erdős Problem 969](https://www.erdosproblems.com/969)
- Moser, L. and MacLeod, R. A., *The error term for the squarefree integers*.
  Canadian Mathematical Bulletin **9** (1966), 303–306.
  https://doi.org/10.4153/CMB-1966-039-4
-/

@[expose] public section

namespace Erdos969

open Filter Asymptotics

/-- The squarefree counting function `Q(x)`. -/
def squarefreeCounting (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter Squarefree).card

/-- Exactly seven integers in $[1,10]$ are squarefree, including $1$. -/
@[category test, AMS 11]
theorem squarefreeCounting_ten : squarefreeCounting 10 = 7 := by
  decide +kernel

/-- The error term in `Q(x) = (6 / π^2) x + E(x)`. -/
noncomputable def squarefreeCountingError (x : ℕ) : ℝ :=
  (squarefreeCounting x : ℝ) - 6 / Real.pi ^ 2 * x

def erdos_969.answer : ℕ → ℝ := sorry

/-- Let $Q(x)$ count the squarefree integers in $[1,x]$, and define $E(x)$ by
$$Q(x)=\frac{6}{\pi^2}x+E(x).$$
Determine the order of magnitude of $E(x)$: an upper bound $E(x)=O(g(x))$ with a matching
oscillation bound $E(x)\ne o(g(x))$. -/
@[category research open, question value, AMS 11]
theorem erdos_969 :
    let g := erdos_969.answer
    (fun x => |squarefreeCountingError x|) =O[atTop] g ∧
      ¬(fun x => |squarefreeCountingError x|) =o[atTop] g := by
  sorry

/-- The prime number theorem implies $E(x)=o(\sqrt{x})$. -/
@[category research solved, AMS 11]
theorem erdos_969.variants.prime_number_theorem :
    (fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ).sqrt) := by
  sorry

/-- Evelyn and Linfoot proved $E(x)=\Omega(x^{1/4})$. -/
@[category research solved, AMS 11]
theorem erdos_969.variants.evelyn_linfoot :
    ¬(fun x => |squarefreeCountingError x|) =o[atTop]
      (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ)) := by
  sorry

end Erdos969
