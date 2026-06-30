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
# Erdős Problem 16

*References:*
- [erdosproblems.com/16](https://www.erdosproblems.com/16)
- [Ch23] Chen, Yong-Gao, A conjecture of Erdős on $p+2^k$. arXiv:2312.04120 (2023).
- [Er50] Erdős, P., On integers of the form $2^k+p$ and some related problems. Summa Brasil. Math.
  (1950), 113-123.
- [Ro34] Romanoff, N. P., Über einige Sätze der additiven Zahlentheorie. Math. Ann. (1934), 668-678.
-/

open Nat Filter Set
open scoped Topology Classical

namespace Erdos16

/--
The set of odd integers not of the form $2^k+p$.
-/
def Erdos16Set : Set ℕ :=
  { n | Odd n ∧ ¬ ∃ k p : ℕ, p.Prime ∧ n = 2 ^ k + p }

/--
A set of natural numbers has density 0.
-/
def density_zero (S : Set ℕ) : Prop :=
  Tendsto (fun x : ℕ ↦ (count S x : ℝ) / (x : ℝ)) atTop (𝓝 0)

/--
Is the set of odd integers not of the form $2^k+p$ the union of an infinite arithmetic progression
and a set of density $0$?

Erdős called this conjecture "rather silly".

Chen [Ch23] has proved the answer is no.

This was formalized in Lean by Chin using Aristotle.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/danielchin/proofs/blob/main/Proofs/ErdosProblems/Erdos16.lean"]
theorem erdos_16 :
    answer(False) ↔
      ∃ A B : Set ℕ, Erdos16Set = A ∪ B ∧
        (∃ a d : ℕ, d > 0 ∧ A = { x | ∃ m : ℕ, x = a + m * d }) ∧
        density_zero B := by
  sorry

/--
A set of natural numbers has positive lower density.
-/
def positive_lower_density (S : Set ℕ) : Prop :=
  0 < atTop.liminf (fun n : ℕ ↦ ((count S n : ℝ) / (n : ℝ) : EReal))

/--
Romanoff [Ro34] showed that the set of odd integers of this form has positive density.
-/
@[category research solved, AMS 11]
theorem erdos_16.variant.romanoff :
    let S := { n : ℕ | Odd n ∧ ∃ k p : ℕ, p.Prime ∧ n = 2 ^ k + p }
    positive_lower_density S := by
  sorry

/--
Using covering congruences Erdős [Er50] proved that the set of odd integers which are not of this
form contains an infinite arithmetic progression.
-/
@[category research solved, AMS 11]
theorem erdos_16.variant.erdos :
    ∃ a d : ℕ, d > 0 ∧ { x | ∃ m : ℕ, x = a + m * d } ⊆ Erdos16Set := by
  sorry

end Erdos16
