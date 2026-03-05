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
# Erdős Problem 984

*Reference:* [erdosproblems.com/984](https://www.erdosproblems.com/984)

Can $\mathbb{N}$ be 2-coloured such that if $\{a, a+d, \ldots, a+(k-1)d\}$ is a $k$-term
monochromatic arithmetic progression then $k \ll_\varepsilon a^\varepsilon$ for all
$\varepsilon > 0$?

A question of Spencer, who proved that this is possible with 3 colours,
with $a^\varepsilon$ replaced by a very slowly growing function $h(a)$ (the inverse of
the van der Waerden function). Erdős reports that he can construct such a
colouring with the bound $k \ll a^{1-c}$ for some absolute constant $c > 0$.

Zach Hunter proved that the answer is yes.

[Er80] Erdős, P., _On some problems in combinatorial number theory_ (1980).
-/

namespace Erdos984

/-- An arithmetic progression $\{a, a+d, \ldots, a+(k-1)d\}$ is monochromatic under
    colouring $c$ if all its elements receive the same colour. -/
def IsMonochromaticAP (c : ℕ → Fin 2) (a d k : ℕ) : Prop :=
  d ≥ 1 ∧ k ≥ 1 ∧ ∃ color : Fin 2, ∀ i : ℕ, i < k → c (a + i * d) = color

/--
Erdős Problem 984 [Er80]:

There exists a 2-colouring of $\mathbb{N}$ such that for every $\varepsilon > 0$, there is a
constant $C > 0$ such that every $k$-term monochromatic arithmetic progression
$\{a, a+d, \ldots, a+(k-1)d\}$ with $a \ge 1$ satisfies $k \le C \cdot a^\varepsilon$.
-/
@[category research solved, AMS 5]
theorem erdos_984 : answer(True) ↔
    ∃ c : ℕ → Fin 2, ∀ ε : ℝ, ε > 0 →
      ∃ C : ℝ, C > 0 ∧ ∀ a d k : ℕ, a ≥ 1 →
        IsMonochromaticAP c a d k →
          (k : ℝ) ≤ C * (a : ℝ) ^ ε := by
  sorry

end Erdos984
