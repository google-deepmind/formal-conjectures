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
# Erdős Problem 187

*Reference:* [erdosproblems.com/187](https://www.erdosproblems.com/187)

Find the best function $f(d)$ such that, in any 2-colouring of the integers,
at least one colour class contains an arithmetic progression with common
difference $d$ of length $f(d)$ for infinitely many $d$.

Originally asked by Cohen. Erdős observed that colouring according to whether
$\{\sqrt{2} \cdot n\} < 1/2$ or not implies $f(d) \ll d$ (using the fact that
$\|\sqrt{2} \cdot q\| \gg 1/q$ for all $q$, where $\|x\|$ is the distance to the
nearest integer). Beck [Be80] improved this using the probabilistic method,
constructing a colouring that shows $f(d) \le (1+o(1))\log_2 d$. Van der Waerden's
theorem implies $f(d) \to \infty$ is necessary.

[Be80] Beck, J., *Roth's estimate of the discrepancy of integer sequences is nearly
sharp*. Combinatorica (1981).

[Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins,
Colo., 1971) (1973), 117-138.

[ErGr79] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory: van der Waerden's theorem and related topics*. Enseign. Math. (1979).

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Real

namespace Erdos187

/-- A 2-colouring $\chi : \mathbb{Z} \to \text{Bool}$ has a monochromatic arithmetic progression of
length $k$ with common difference $d$: there exist a starting point $a \in \mathbb{Z}$ and
a colour $c$ such that $\chi(a + i \cdot d) = c$ for all $0 \le i < k$. -/
def HasMonoAP (χ : ℤ → Bool) (d : ℕ) (k : ℕ) : Prop :=
  ∃ a : ℤ, ∃ c : Bool, ∀ i : ℕ, i < k → χ (a + ↑i * ↑d) = c

/--
Erdős Problem 187 [Er73, ErGr79, ErGr80]:

There exists an absolute constant $c > 0$ such that, for any 2-colouring
$\chi : \mathbb{Z} \to \text{Bool}$, there are infinitely many positive integers $d$ for which $\chi$
has a monochromatic arithmetic progression with common difference $d$ and
length at least $c \cdot \log(d)$.

The upper bound direction is known: Beck [Be80] showed there exists a
2-colouring such that the longest monochromatic AP with common difference
$d$ has length at most $(1+o(1)) \cdot \log_2(d)$. So the best $f(d)$ is $\Theta(\log d)$
if this conjecture holds.
-/
@[category research open, AMS 5 11]
theorem erdos_187 :
    ∃ c : ℝ, 0 < c ∧
    ∀ χ : ℤ → Bool,
    ∀ N : ℕ, ∃ d : ℕ, N < d ∧
      ∃ k : ℕ, c * Real.log ↑d ≤ ↑k ∧ HasMonoAP χ d k := by
  sorry

end Erdos187
