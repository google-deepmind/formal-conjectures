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
# Erdős Problem 1096

*References:*
- [erdosproblems.com/1096](https://www.erdosproblems.com/1096)
- [ErKo98] Erdős, P. and Komornik, V., Developments in non-integer bases.
  Acta Math. Hungar. (1998), 57--83.
- [Fe16] Feng, D.-J., On the topology of polynomials with bounded integer coefficients.
  J. Eur. Math. Soc. (2016), 181--193.
-/

open Filter
open scoped Topology

namespace Erdos1096

/--
Let $1<q<1+\epsilon$ and consider the set of numbers of the shape
$\sum_{i\in S}q^i$ (for all finite $S$), ordered by size as
$0=x_1<x_2<\cdots$.

Is it true that, provided $\epsilon>0$ is sufficiently small, $x_{k+1}-x_k \to 0$?

This was solved affirmatively by Erdős and Komornik [ErKo98], who proved the conclusion
whenever $1<q<\sqrt{q_1}$, where $q_1$ is the second Pisot-Vijayaraghavan number.
-/
@[category research solved, AMS 11]
theorem erdos_1096 :
    answer(True) ↔ ∃ ε > 0, ∀ q, 1 < q → q < 1 + ε →
    ∀ x : ℕ → ℝ, StrictMono x → Set.range x = { ∑ i ∈ S, q ^ i | S : Finset ℕ } →
    Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) := by
  sorry

-- TODO: add variants and additional material from the Erdős Problems page.

end Erdos1096
