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
# Erdős Problem 650

*Reference:* [erdosproblems.com/650](https://www.erdosproblems.com/650)

Let $f(m)$ denote the largest number guaranteed such that for every $N \geq 1$,
every $m$-element subset $A \subseteq \{1, \ldots, N\}$, and every $t \geq 1$,
the interval $[t, t+2N)$ contains at least $f(m)$ integers that can be matched
to distinct elements of $A$ by divisibility. Erdős and Sarányi proved
$f(m) \gg m^{1/2}$; is it true that $f(m) \ll m^{1/2}$? The answer is yes:
Erdős and Selfridge established $f(m) \ll m^{1/2}$.

[Er95c] Erdős, P., _Some problems in number theory_. Octogon Math. Mag. (1995), 3–5.

[Er78] Erdős, P., _Problems and results in combinatorial analysis and combinatorial
  number theory_, Proceedings of the Ninth Southeastern Conference on Combinatorics,
  Graph Theory, and Computing (1978), 29–40.

[Er86c] Erdős, P., _Some problems on number theory_ (1986), 53–67.

[ErSa59] Erdős, P. and Sarányi, J., _Über ein Extremalproblem_. Matematikai Lapok (1959).
-/

namespace Erdos650

/-- The divisibility matching number: given a finite set $A$ of positive integers,
a starting point $t \geq 1$, and a parameter $N$, this is the maximum $r$ such that
there exist $r$ distinct integers $b_1, \ldots, b_r$ in $[t, t + 2N)$ and $r$ distinct
elements $a_1, \ldots, a_r \in A$ with $a_i \mid b_i$. -/
noncomputable def divMatchCount (A : Finset ℕ) (t N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ (b a : Fin r → ℕ),
    Function.Injective b ∧ Function.Injective a ∧
    (∀ i, a i ∈ A) ∧
    (∀ i, t ≤ b i ∧ b i < t + 2 * N) ∧
    (∀ i, a i ∣ b i)}

/-- $f(m)$: the largest value guaranteed in all configurations. For every $N \geq 1$
and every $m$-element subset $A$ of $\{1, \ldots, N\}$, every interval $[t, t+2N)$ with
$t \geq 1$ contains at least $f(m)$ matchable integers. -/
noncomputable def erdos650F (m : ℕ) : ℕ :=
  sInf {c : ℕ | ∃ (N : ℕ) (A : Finset ℕ) (t : ℕ),
    A.card = m ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ t ≥ 1 ∧
    divMatchCount A t N = c}

/--
Erdős Problem 650 [Er95c]:

Is it true that $f(m) \ll m^{1/2}$? Erdős and Sarányi [ErSa59] proved $f(m) \gg m^{1/2}$,
so this would establish $f(m) \asymp m^{1/2}$. The answer is yes, proved by Erdős and
Selfridge [Er78] [Er86c].
-/
@[category research solved, AMS 5 11]
theorem erdos_650 : answer(True) ↔
    (fun m => (erdos650F m : ℝ)) ≪ (fun m => Real.sqrt (m : ℝ)) := by
  sorry

/--
Erdős Problem 650, stronger variant:

$f(st) \leq s + t$ for all integers $s, t \geq 1$, which implies
$f(m) \leq 2\lceil\sqrt{m}\rceil$.
-/
@[category research solved, AMS 5 11]
theorem erdos_650_strong :
    ∀ s t : ℕ, 1 ≤ s → 1 ≤ t → erdos650F (s * t) ≤ s + t := by
  sorry

end Erdos650
