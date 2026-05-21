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
# Erdős Problem 1029

*References:*
- [erdosproblems.com/1029](https://www.erdosproblems.com/1029)
- [ErSz35] Erdős, P. and Szekeres, G., *A combinatorial problem in geometry*, Compositio
  Math. 2 (1935), 463–470.
- [Sp75] Spencer, J., *Ramsey's theorem — a new lower bound*, J. Combin. Theory Ser. A 18
  (1975), 108–115.
- [Er93] Erdős, P., *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333–350.
-/

open Filter Finset SimpleGraph

namespace Erdos1029

/--
Erdős Problem 1029 [Er93, p.337]:

$R(k) / (k \cdot 2^{k/2}) \to \infty$ as $k \to \infty$.

Here $R(k)$ is the diagonal Ramsey number, expressed as `diagRamseyNumber k`.
-/
@[category research open, AMS 5]
theorem erdos_1029 :
    Tendsto (fun k : ℕ =>
      (diagRamseyNumber k : ℝ) / ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)))
      atTop atTop := by
  sorry

-- TODO: Formalize the Erdős–Szekeres upper bound R(k) ≤ C(2k-2, k-1) and
-- Spencer's lower bound R(k) ≥ (1+o(1)) · (√2/e) · k · 2^{k/2}.

end Erdos1029
