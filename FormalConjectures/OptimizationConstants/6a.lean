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
# Tao's Optimization Constant 6a / The Union-Closed Sets Conjecture

*References:*
- [Tao's Optimization Constant 6a](https://teorth.github.io/optimizationproblems/constants/6a.html)
- [F1995] Frankl, P., *Extremal set systems*. Handbook of Combinatorics (1995).
- [AHS2022] Alweiss, R., Huang, B. and Sellke, M., *Improved lower bound for the union-closed sets
  conjecture*. [arXiv:2211.11731](https://arxiv.org/abs/2211.11731)
- [CL2022] Chase, Z. and Lovett, S., *Approximate union closed conjecture*.
  [arXiv:2211.11689](https://arxiv.org/abs/2211.11689)
- [S2022] Sawin, W., *An improved lower bound for the union-closed set conjecture*.
  [arXiv:2211.11504](https://arxiv.org/abs/2211.11504)
- [C2022] Cambie, S., *Better bounds for the union-closed sets conjecture using the entropy
  approach*. [arXiv:2212.12500](https://arxiv.org/abs/2212.12500)
- [Y2022] Yu, L., *Dimension-free bounds for the union-closed sets conjecture*.
  [arXiv:2212.00658](https://arxiv.org/abs/2212.00658)
- [L2023] Liu, J., *Improving the lower bound for the union-closed sets conjecture via
  conditionally IID coupling*. [arXiv:2306.08824](https://arxiv.org/abs/2306.08824)
-/

@[expose] public section

open Finset

namespace Constant6a

/-- **Tao's Optimization Constant 6a / The union-closed sets conjecture**: the largest $c$ such
that every union-closed family $A \ne \{\emptyset\}$ of finite subsets of $\mathbb{N}$ (or any infinite set/type) has an
element that belongs to at least a $c$ fraction of its sets. -/
@[optimization_constant "6a"]
noncomputable def C6a : ℝ :=
  sSup {c : ℝ | ∀ (A : Finset (Finset ℕ)), A ≠ {∅} →
    (∀ᵉ (X ∈ A) (Y ∈ A), X ∪ Y ∈ A) → ∃ i, c * #A ≤ #{x ∈ A | i ∈ x}}

/-- The union-closed sets conjecture of Frankl: $C_{6a} = 1/2$. -/
@[category research open, AMS 5]
theorem c6a_eq_half : C6a = 1 / 2 := by
  sorry

/-- The upper bound $C_{6a} \le 1/2$ [F1995]. It holds because in the family of all subsets of a
finite set, every element belongs to exactly half of the sets. -/
@[category research solved, AMS 5]
theorem c6a_upper_bound : C6a ≤ 1 / 2 := by
  sorry

/-- Can the best known upper bound $1/2$ be improved? -/
@[category research open, question, AMS 5]
theorem c6a_upper_bound_improved : C6a < 1 / 2 := by
  sorry

/-- The first lower bound, $(3 - \sqrt 5) / 2$, proved independently in [AHS2022], [CL2022] and
[S2022]. -/
@[category research solved, AMS 5]
theorem c6a_lower_bound_first : (3 - Real.sqrt 5) / 2 ≤ C6a := by
  sorry

/-- An intermediate lower bound, proved in [C2022] and [Y2022]. -/
@[category research solved, AMS 5]
theorem c6a_lower_bound_intermediate : 0.38234 ≤ C6a := by
  sorry

/-- The best known lower bound, proved by Liu in [L2023]. -/
@[category research solved, AMS 5]
theorem c6a_lower_bound : 0.38271 ≤ C6a := by
  sorry

/-- Can the best known lower bound $0.38271$ of [L2023] be improved? -/
@[category research open, question, AMS 5]
theorem c6a_lower_bound_improved : 0.38272 < C6a := by
  sorry

end Constant6a
