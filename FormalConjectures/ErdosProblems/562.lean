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
# Erdős Problem 562

*Reference:* [erdosproblems.com/562](https://www.erdosproblems.com/562)
-/

open Combinatorics Filter Real
open scoped Asymptotics

namespace Erdos562

/--
Let $R_r(n)$ denote the $r$-uniform hypergraph Ramsey number: the minimal $m$ such that if we
$2$-colour all edges of the complete $r$-uniform hypergraph on $m$ vertices then there must be some
monochromatic copy of the complete $r$-uniform hypergraph on $n$ vertices.

Prove that, for $r \ge 3$,
$$ \log_{r-1} R_r(n) \asymp_r n, $$
where $\log_{r-1}$ denotes the $(r-1)$-fold iterated logarithm.
-/
@[category research open, AMS 05]
theorem erdos_562 : answer(sorry) ↔
    ∀ r ≥ 3, (fun n ↦ log^[r - 1] (hypergraphRamsey r n)) ~[atTop] (fun n ↦ (n : ℝ)) := by
  sorry

/--
For $r = 3$, the lower bound $R_3(n) \geq 2^{2^{cn}}$ for some $c > 0$ is an open problem
(see Problem 564). The upper bound tower-type $R_3(n) \leq \exp\exp(cn)$ is classical
(Erdős and Rado), giving one direction of the asymptotic equivalence of $\log\log R_3(n) \asymp n$.
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/562", AMS 05]
theorem erdos_562.variants.known_result :
    ∃ c > 0, ∀ᶠ n in atTop, (hypergraphRamsey 3 n : ℝ) ≤ Real.exp (Real.exp (c * n)) := by
  sorry

end Erdos562
