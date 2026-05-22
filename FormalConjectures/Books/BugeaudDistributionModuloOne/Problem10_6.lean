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
# Bugeaud Collection of Conjectures and Open Questions: Rapidly Increasing Sequences Dense Modulo One

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
-/

namespace Bugeaud

/--
Problem 10.6. Find a very rapidly increasing sequence $(m_n)_{n \ge 1}$ of positive
integers such that $(\{\xi m_n\})_{n \ge 1}$ is dense modulo one for every irrational
number $\xi$.

Here "very rapidly increasing" is formalised by requiring that $(m_n)$ is lacunary,
i.e. there exists $c > 1$ with $c \cdot m_n < m_{n+1}$ for all sufficiently large $n$.
-/
@[category research open, AMS 11]
theorem problem_10_6 :
    ∃ m : ℕ → ℕ, (∀ n, 0 < m n) ∧ IsLacunary m ∧
      ∀ ξ : ℝ, Irrational ξ → Dense (Set.range fun n => Int.fract (ξ * m n)) := by
  sorry

end Bugeaud
