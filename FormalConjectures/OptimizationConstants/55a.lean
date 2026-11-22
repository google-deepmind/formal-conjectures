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
# Tao's Optimization Constant 55a / Coefficient of the acyclic chromatic index

*References:*
* Tao's optimization constant 55a:
  <https://teorth.github.io/optimizationproblems/constants/55a.html>
* [AMR1991] N. Alon, C. McDiarmid, B. Reed, *Acyclic coloring of graphs*, Random Structures
  Algorithms 2(3) (1991), 277–288.
* [MR1998] M. Molloy, B. Reed, *Further algorithmic aspects of the local lemma*, Proc. 30th ACM
  Symposium on Theory of Computing (STOC 1998), 524–529.
* [ASZ01] N. Alon, B. Sudakov, A. Zaks, *Acyclic edge colorings of graphs*,
  J. Graph Theory 37 (2001), 157–167. [doi:10.1002/jgt.1010](https://doi.org/10.1002/jgt.1010)
* [EP2013] L. Esperet, A. Parreau, *Acyclic edge-coloring using entropy compression*,
  European J. Combin. 34(6) (2013), 1019–1027. [arXiv:1206.1535](https://arxiv.org/abs/1206.1535)
* [FLM2020] P. M. S. Fialho, B. N. B. de Lima, A. Procacci, *A new bound on the acyclic edge
  chromatic number*, Discrete Math. 343(11) (2020), 112037.
  [arXiv:1912.04436](https://arxiv.org/abs/1912.04436)
* [KLS2026] L. Kirousis, J. Livieratos, A. Singh, *An improvement on the bound for the acyclic
  chromatic index* (2026). [arXiv:2602.14859](https://arxiv.org/abs/2602.14859)
-/

@[expose] public section

open SimpleGraph Asymptotics Filter

namespace Constant55a

/-- **Tao's Optimization Constant 55a / Coefficient of the acyclic chromatic index**:
the infimum of all $c$ such that for all finite simple graphs $G$,
$\chi_a'(G) \le c\Delta + o(\Delta)$, where $\chi_a'(G)$ is the acyclic chromatic
index (`SimpleGraph.acyclicChromaticIndex`) and $\Delta$ the maximum degree of $G$. -/
@[optimization_constant "55a"]
noncomputable def C55a : ℝ :=
  sInf {c : ℝ | ∃ o : ℕ → ℝ, o =o[atTop] (fun d ↦ (d : ℝ)) ∧
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (G.acyclicChromaticIndex : ℝ) ≤ c * G.maxDegree + o G.maxDegree}

/-- $C_{55}$ is conjectured to be $1$. This would follow from the acyclic edge coloring
conjecture $\chi_a'(G) \le \Delta + 2$ [ASZ01, Conjecture 1]. -/
@[category research open, AMS 5]
theorem c55a_eq_one : C55a = 1 := by
  sorry

/-- The trivial lower bound: $\chi_a'(G) \ge \Delta(G)$, since the edges at a vertex of maximum
degree need distinct colours, and stars $K_{1,n}$ have arbitrarily large maximum degree. -/
@[category research solved, AMS 5]
theorem c55a_lower_bound : 1 ≤ C55a := by
  sorry

/-- Can the trivial lower bound $1$ be improved? A positive answer would disprove the
acyclic edge coloring conjecture. -/
@[category research open, question, AMS 5]
theorem c55a_lower_bound_improved : 1 < C55a := by
  sorry

/-- The first upper bound: $\chi_a'(G) \le 64\Delta$ [AMR1991], improved to
$\chi_a'(G) \le 16\Delta$ [MR1998]. -/
@[category research solved, AMS 5]
theorem c55a_upper_bound_first : C55a ≤ 16 := by
  sorry

/-- An intermediate upper bound: $\chi_a'(G) \le 4(\Delta - 1)$ [EP2013]. -/
@[category research solved, AMS 5]
theorem c55a_le_4 : C55a ≤ 4 := by
  sorry

/-- An intermediate upper bound: $\chi_a'(G) \le 3.569(\Delta - 1)$ [FLM2020]. -/
@[category research solved, AMS 5]
theorem c55a_le_3_569 : C55a ≤ 3.569 := by
  sorry

/-- The best known upper bound: $\chi_a'(G) \le 3.142(\Delta - 1) + 1$ [KLS2026]. -/
@[category research solved, AMS 5]
theorem c55a_upper_bound : C55a ≤ 3.142 := by
  sorry

/-- Can the best known upper bound $3.142$ be improved? -/
@[category research open, question, AMS 5]
theorem c55a_upper_bound_improved : C55a < 3.142 := by
  sorry

end Constant55a
