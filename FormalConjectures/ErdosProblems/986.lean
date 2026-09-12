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
# Erdős Problem 986

*References:*
- [erdosproblems.com/986](https://www.erdosproblems.com/986)
- [ChGr98] Chung, F. and Graham, R., *Erdős on Graphs: His Legacy of Unsolved Problems*.
  A K Peters, Ltd. (1998).
- [Br26] Bradač, D., Off-diagonal Ramsey numbers. arXiv:2605.28793 (2026).
- [Sp77] Spencer, J., Asymptotic lower bounds for Ramsey functions. Discrete Math. (1977), 69-76.
- [MaVe23] Mattheus, S. and Verstraëte, J., The asymptotics of $r(4,t)$. Ann. of Math. (2024),
  941-965.
-/

open Filter

namespace Erdos986

/--
For any fixed $s\geq 3$,
$$R(s,k) \gg \frac{k^{s-1}}{(\log k)^c}$$
for some constant $c=c(s)>0$.

According to Chung and Graham [ChGr98] this was first conjectured by Erdős in 1947.

Proved by Bradač [Br26], with $c=2s-4$.
-/
@[category research solved, AMS 5]
theorem erdos_986 :
    ∀ (s : ℕ) (hs : 3 ≤ s),
      ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
        ∀ᶠ (k : ℕ) in atTop,
          (SimpleGraph.classicalRamsey s k : ℝ) ≥
            C * (k : ℝ) ^ (s - 1) / (Real.log k) ^ c := by
  sorry

-- TODO: Add variants of the problem.

end Erdos986
