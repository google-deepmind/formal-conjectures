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
# Erdős Problem 315

*Reference:* [erdosproblems.com/315](https://www.erdosproblems.com/315)

Is it true that the Sylvester (greedy) sequence uniquely maximizes the growth rate
among all Egyptian fraction representations of 1? That is, if
$a_0 < a_1 < \ldots$ is any strictly increasing sequence of positive integers with
$\sum 1/a_n = 1$ other than the Sylvester sequence, is $\liminf a_n^{1/2^n} < c_0$,
where $c_0$ is the Vardi constant?

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number theory_.
Monographies de L'Enseignement Mathématique (1980).

[Ka25] Kamio, Y., _Asymptotic analysis of infinite decompositions of a unit fraction into unit
fractions_. arXiv:2503.02317 (2025).

[LiTa25] Li, Z. and Tang, Q., _On a conjecture of Erdős and Graham about the Sylvester's sequence_.
arXiv:2503.12277 (2025).

See also OEIS sequences A000058 and A076393.
-/

open Filter

open scoped Topology

namespace Erdos315

/-- The auxiliary sequence $u_0 = 1$, $u_{n+1} = u_n(u_n + 1)$,
    giving $1, 2, 6, 42, 1806, \ldots$ -/
def sylvesterU : ℕ → ℕ
  | 0 => 1
  | n + 1 => sylvesterU n * (sylvesterU n + 1)

/-- The Sylvester sequence $s_n = u_n + 1$, giving $2, 3, 7, 43, 1807, \ldots$
    This is the greedy Egyptian fraction representation of $1$:
    $\sum_n 1/s_n = 1$. -/
def sylvesterSeq (n : ℕ) : ℕ := sylvesterU n + 1

/--
Erdős Problem 315 [ErGr80, p.41]:

The Sylvester sequence $(2, 3, 7, 43, 1807, \ldots)$ is defined by $s_0 = 2$ and
$s_{n+1} = s_n^2 - s_n + 1$. It satisfies $\sum 1/s_n = 1$ and
$\lim s_n^{1/2^n} = c_0 \approx 1.264085\ldots$ (the Vardi constant).

The conjecture states: if $a_0 < a_1 < a_2 < \ldots$ is any strictly increasing
sequence of positive integers with $\sum 1/a_n = 1$, other than the Sylvester
sequence, then $\liminf a_n^{1/2^n} < c_0$. In other words, the Sylvester (greedy)
representation uniquely maximizes the growth rate $\liminf$.

This was proved independently by Kamio [Ka25] and Li–Tang [LiTa25] in 2025.
-/
@[category research solved, AMS 11 40]
theorem erdos_315 : answer(True) ↔
    ∀ (a : ℕ → ℕ),
      StrictMono a →
      (∀ n, 0 < a n) →
      HasSum (fun n => (1 : ℝ) / (a n : ℝ)) 1 →
      a ≠ sylvesterSeq →
      Filter.liminf (fun n => (a n : ℝ) ^ ((2 : ℝ) ^ (n : ℕ))⁻¹) atTop <
        Filter.liminf (fun n => (sylvesterSeq n : ℝ) ^ ((2 : ℝ) ^ (n : ℕ))⁻¹) atTop := by
  sorry

end Erdos315
