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
# Erdős Problem 969

*Reference:* [Erdős Problem 969](https://www.erdosproblems.com/969)
-/

namespace Erdos969

open Filter Asymptotics

/-- The squarefree counting function `Q(x)`. -/
def squarefreeCounting (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter Squarefree).card

/-- The error term in `Q(x) = (6 / π^2) x + E(x)`. -/
noncomputable def squarefreeCountingError (x : ℕ) : ℝ :=
  (squarefreeCounting x : ℝ) - 6 / Real.pi ^ 2 * x

/-- Let $Q(x)$ count the squarefree integers in $[1,x]$, and define $E(x)$ by
$$Q(x)=\frac{6}{\pi^2}x+E(x).$$
Determine the order of magnitude of $E(x)$. The two estimates below explicitly say that the
answer is both an asymptotic upper and lower bound for $|E(x)|$. -/
@[category research open, AMS 11]
theorem erdos_969 :
    let g := (answer(sorry) : ℕ → ℝ)
    (fun x => |squarefreeCountingError x|) =O[atTop] g ∧
      g =O[atTop] (fun x => |squarefreeCountingError x|) := by
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
