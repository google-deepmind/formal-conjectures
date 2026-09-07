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
# Erdős Problem 57

*References:*
- [erdosproblems.com/57](https://www.erdosproblems.com/57)
- [ErHa66] Erdős, P. and Hajnal, A., *On chromatic number of graphs and set-systems*. Acta Math. Acad. Sci. Hungar. (1966), 61-99.
- [LiMo20] Liu, Hong and Montgomery, Richard, *A solution to Erdős and Hajnal's odd cycle problem*. arXiv:2010.15802 (2020).
-/

namespace Erdos57

/--
If $G$ is a graph with infinite chromatic number and $a_1 < a_2 < \cdots$ are lengths of the odd
cycles of $G$ then $\sum \frac{1}{a_i} = \infty$.

Conjectured by Erdős and Hajnal [ErHa66], and solved by Liu and Montgomery [LiMo20].
-/
@[category research solved, AMS 5]
theorem erdos_57 :
    ∀ {V : Type*} (G : SimpleGraph V), G.chromaticNumber = ⊤ →
      ¬ Summable (fun (a : G.oddCycleLengths) ↦ 1 / (a : ℝ)) := by
  sorry

end Erdos57
