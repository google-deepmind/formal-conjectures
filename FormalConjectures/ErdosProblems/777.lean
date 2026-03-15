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
# Erdős Problem 777

*Reference:* [erdosproblems.com/777](https://www.erdosproblems.com/777)

Three questions of Daykin and Erdős on comparability graphs of families of subsets.

The first question was answered affirmatively by Alon, Das, Glebov, and Sudakov.
The second question was answered negatively by Alon and Frankl.
The third question was answered affirmatively by Alon and Frankl.

[Gu83] Guy, R.K., _Unsolved Problems in Number Theory_, 1983.
[ADGS15] Alon, N., Das, S., Glebov, R., Sudakov, B., _Comparable pairs in families of sets_.
  J. Combin. Theory Ser. B **114** (2015), 164–185.
[AlFr85] Alon, N., Frankl, P., _The maximum number of disjoint pairs in a family of subsets_.
  Graphs Combin. **1** (1985), 13–21.
-/

namespace Erdos777

/--
The number of edges of the comparability graph of a family $F$ of subsets of
$\mathrm{Fin}(n)$: counts pairs $(A, B)$ in $F \times F$ with $A \subsetneq B$.
Since the filter is asymmetric ($A \subsetneq B$ does not imply $B \subsetneq A$),
each unordered comparable pair is counted exactly once.
-/
def comparableEdges (n : ℕ) (F : Finset (Finset (Fin n))) : ℕ :=
  ((F ×ˢ F).filter (fun p => p.1 ≠ p.2 ∧ p.1 ⊆ p.2)).card

/--
**Erdős Problem 777, Question 1** (solved, affirmative — Alon–Das–Glebov–Sudakov):

For all $\varepsilon > 0$, if $n$ is sufficiently large and $F$ is a family of at most
$\lfloor (2 - \varepsilon) \cdot 2^{n/2} \rfloor$ subsets of $\{0, \ldots, n-1\}$, then the
comparability graph of $F$ has fewer than $2^n$ edges.
-/
@[category research solved, AMS 5]
theorem erdos_777 : answer(True) ↔
    ∀ ε : ℝ, ε > 0 → ε < 2 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ F : Finset (Finset (Fin n)),
        (F.card : ℝ) ≤ (2 - ε) * (2 : ℝ) ^ ((n : ℝ) / 2) →
        comparableEdges n F < 2 ^ n := by
  sorry

/--
**Erdős Problem 777, Question 2** (solved, negative — Alon–Frankl):

Is it true that if the comparability graph of $F$ has at least $c \cdot |F|^2$ edges,
then $|F| \ll_c 2^{n/2}$? The answer is no.
-/
@[category research solved, AMS 5]
theorem erdos_777.variants.q2 : answer(False) ↔
    ∀ c : ℝ, c > 0 →
    ∃ C : ℝ, C > 0 ∧
      ∀ (n : ℕ) (F : Finset (Finset (Fin n))),
        (comparableEdges n F : ℝ) ≥ c * (F.card : ℝ) ^ 2 →
        (F.card : ℝ) ≤ C * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  sorry

/--
**Erdős Problem 777, Question 3** (solved, affirmative — Alon–Frankl):

For all $\varepsilon > 0$, there exists $\delta > 0$ such that for all $n$ and every family $F$ of
subsets of $\{0, \ldots, n-1\}$, if the number of comparable pairs exceeds $|F|^{2 - \delta}$,
then $|F| < (2 + \varepsilon)^{n/2}$.
-/
@[category research solved, AMS 5]
theorem erdos_777.variants.q3 : answer(True) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ δ : ℝ, δ > 0 ∧
      ∀ (n : ℕ) (F : Finset (Finset (Fin n))),
        (comparableEdges n F : ℝ) > (F.card : ℝ) ^ ((2 : ℝ) - δ) →
        (F.card : ℝ) < ((2 : ℝ) + ε) ^ ((n : ℝ) / 2) := by
  sorry

end Erdos777
