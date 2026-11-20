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
# Tao's Optimization constant 4a / The cap set constant

*References:*
- [Tao's optimization constant 4a](https://teorth.github.io/optimizationproblems/constants/4a.html)
- [EG2016] Ellenberg, J. S. and Gijswijt, D., *On large subsets of F_q^n with no
  three-term arithmetic progression* (https://doi.org/10.4007/annals.2017.185.1.8)
- [ZWLPLZJZZZ2025] Zhai, Y., Wei, Z., Li, R., Pan, K., Liu, S., Zhang, L., Ji, J., Zhang, W., Zhang, Y. and Zhang, Y., 2025. (X)-evolve: Solution space evolution powered by large language models. https://arxiv.org/abs/2508.07932
-/

@[expose] public section

open Filter Finset

namespace Constant4a
/-- **Tao's Optimization constant 4a / The cap set constant**:
The smallest constant $C$ such that $r(n) \leq C^{(1+o(1)) n}$, where $r(n)$ is the size of the largest cap set in $\mathbb{F}_{3}^{n}$, i.e., a set that does not contain any lines (length three progressions).
-/

@[optimization_constant "4a"]
noncomputable def C4a : ℝ :=
  sSup {(sSup (card '' {A : Finset (GaloisField 3 n) |
  ThreeAPFree (A : Set (GaloisField 3 n))})) ^ (1 / (n : ℝ)) | n > 0}

set_option linter.style.formal_proof_palomar false in
/-- The best known upper bound, $3/8 \sqrt[3]{207+33\sqrt{33}}$, proved in [EG2016]. -/
@[category research solved, AMS 5, formal_proof using other_system at "https://github.com/lean-forward/cap_set_problem/blob/095a2f18f81c551a0053f2e65806de751e438fc4/src/section_13b.lean#L786"]
theorem c4a_upper_bound : C4a ≤ 3 / 8 * (207 + 33 * √ 33) ^ (1 / (3 : ℝ)) := by
  sorry

/-- Can the best known upper bound $3/8 \sqrt[3]{207+33\sqrt{33}} \approx 2.756$ be improved? -/
@[category research open, question, AMS 5]
theorem c4a_upper_bound_improved : C4a < 3 / 8 * (207 + 33 * √ 33) ^ (1 / (3 : ℝ)) := by
  sorry

/-- The best know lower bound, $2.2203$, from [ZWLPLZJZZZ2025] -/
@[category research solved, AMS 5]
theorem c4a_lower_bound : C4a > 2.2203 := by
  sorry

def c4a_eq.answer : ℝ := sorry

/-- What is the exact value of the constant? -/
@[category research open, question value, AMS 5]
theorem c4a_eq : C4a = c4a_eq.answer := by
  sorry

end Constant4a
