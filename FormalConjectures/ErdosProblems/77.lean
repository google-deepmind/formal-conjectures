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
# Erdős Problem 77

*Reference:* [erdosproblems.com/77](https://www.erdosproblems.com/77)

If $R(k)$ is the diagonal Ramsey number, the minimal $n$ such that every 2-colouring
of the edges of $K_n$ contains a monochromatic copy of $K_k$, then find the value of
$$\lim_{k \to \infty} R(k)^{1/k}.$$

Erdős proved $\sqrt{2} \leq \liminf R(k)^{1/k} \leq \limsup R(k)^{1/k} \leq 4$.
The upper bound has been improved to $3.7992\ldots$ by Gupta, Ndiaye, Norin, and
Wei [GNNW24], building on the breakthrough of Campos, Griffiths, Morris,
and Sahasrabudhe [CGMS23] who first improved the upper bound below 4.

Erdős offered \$250 for solving this problem.

[CGMS23] Campos, M., Griffiths, S., Morris, R., and Sahasrabudhe, J.,
_An exponential improvement for diagonal Ramsey_. (2023).

[GNNW24] Gupta, A., Ndiaye, M., Norin, S., and Wei, F.,
_An improved upper bound for diagonal Ramsey numbers_. (2024).
-/

open Filter

open scoped Topology

namespace Erdos77

/-- The diagonal Ramsey number $R(k)$: the minimum $N$ such that for every
symmetric 2-colouring of the edges of $K_N$, there is a monochromatic
clique of size $k$ in some colour. -/
noncomputable def diagonalRamseyNumber (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Bool), (∀ i j, c i j = c j i) →
    ∃ (b : Bool) (S : Finset (Fin N)), S.card = k ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = b}

/--
Erdős Problem 77:

Find the value of $\lim_{k \to \infty} R(k)^{1/k}$, where $R(k)$ is the diagonal
Ramsey number.
-/
@[category research open, AMS 5]
theorem erdos_77 :
    Tendsto (fun k : ℕ =>
      (diagonalRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop (nhds (answer(sorry) : ℝ)) := by
  sorry

end Erdos77
