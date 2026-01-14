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
# Ben Green's Open Problem 49

*Reference:*
https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.49
-/

open Pointwise

namespace Green49

/--
Ben Green's Open Problem 49 (Polynomial Freiman–Ruzsa conjecture over $\mathbb{F}_2^n$).

Suppose that $A \subset \mathbb{F}_2^n$ satisfies $|A + A| \le K |A|$.
Is it true that $A$ is covered by $K^{O(1)}$ translates of a subspace
of size at most $|A|$?

This problem is now solved, following the Polynomial Freiman–Ruzsa theorem
proved by Gowers, Green, Manners, and Tao (2023).
See: https://arxiv.org/abs/2311.05762
-/
@[category research solved, AMS 05 11]
theorem green_49 : answer(True) ↔
  ∃ C > 0,
    ∀ (n : ℕ) (K : ℝ) (A : Finset (Fin n → ZMod 2)),
      1 ≤ K →
      ((A + A).card : ℝ) ≤ K * A.card →
      ∃ V : Submodule (ZMod 2) (Fin n → ZMod 2),
        (Nat.card V ≤ A.card) ∧
        ∃ (t : Finset (Fin n → ZMod 2)),
          t.card ≤ K ^ C ∧
          A ⊆ t.bind (fun x => x +ᵥ V) := by
  sorry

end Green49
