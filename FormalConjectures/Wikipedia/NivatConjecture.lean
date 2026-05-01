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
# Nivat conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Nivat_conjecture)
-/

namespace NivatConjecture

variable {A : Type*} [Finite A]

/-- The **block complexity** of a configuration `x : ℤ × ℤ → A` at scale `n × m` is the number
of distinct `n × m` rectangular patterns appearing in `x`. -/
noncomputable def blockComplexity (x : ℤ × ℤ → A) (n m : ℕ) : ℕ :=
  (Set.range fun (p : ℤ × ℤ) => fun (q : Fin n × Fin m) =>
    x (p.1 + (q.1 : ℤ), p.2 + (q.2 : ℤ))).ncard

/-- A configuration `x : ℤ × ℤ → A` is **periodic** if there exists a nonzero vector
`v : ℤ × ℤ` such that translating by `v` leaves `x` invariant. -/
def IsPeriodic (x : ℤ × ℤ → A) : Prop :=
  ∃ v : ℤ × ℤ, v ≠ 0 ∧ Function.Periodic x v

/-- The **Nivat conjecture**: if there exist integers `n, m ≥ 1` such that the block complexity
satisfies `P_x(n, m) ≤ n * m`, then the configuration `x` is periodic.
-/
@[category research open, AMS 37 68]
theorem nivat_conjecture answer(sorry) ↔ (x : ℤ × ℤ → A) :
    (∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ blockComplexity x n m ≤ n * m) → IsPeriodic x := by
  sorry

end NivatConjecture
