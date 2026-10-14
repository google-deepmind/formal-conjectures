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
# Nivat conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Nivat%27s_Conjecture)
- M. Nivat, invited talk at ICALP 1997 (Bologna), where the conjecture was first stated.
- [Nonexpansive $\mathbb{Z}^2$-subdynamics and Nivat's conjecture](https://arxiv.org/abs/1208.4090)
  by *Van Cyr and Bryna Kra*, Trans. Amer. Math. Soc. 367 (2015), 6487–6537.
- [An algebraic geometric approach to Nivat's conjecture](https://arxiv.org/abs/1510.00177)
  by *Jarkko Kari and Michal Szabados*, Information and Computation 271 (2020).
-/

@[expose] public section

namespace NivatConjecture

/-- The **Nivat conjecture**: if there exist integers $n, m \ge 1$ such that the block complexity
satisfies $P_x(n, m) \le n m$, then the configuration $x$ is periodic.
-/
@[category research open, AMS 37 68]
theorem nivat_conjecture :
    answer(sorry) ↔ ∀ (A : Type) [Finite A] (x : ℤ × ℤ → A),
      (∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ blockComplexity x n m ≤ n * m) → IsPeriodic x := by
  sorry

end NivatConjecture
