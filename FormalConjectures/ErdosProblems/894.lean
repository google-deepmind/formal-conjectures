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
# Erdős Problem 894

Is it true that for every lacunary sequence $A \subset \mathbb{N}$, there exists a finite colouring
of $\mathbb{N}$ with no monochromatic pair whose difference lies in $A$?

[Ka01] Katznelson, Y., _Chromatic numbers of Cayley graphs on ℤ and recurrence_.
Combinatorica (2001), 211–219.

[PeSc10] Peres, Y., Schlag, W., _Two Erdős problems on lacunary sequences: chromatic
number and Diophantine approximation_. Bull. Lond. Math. Soc. (2010), 295–300.

*Reference:* [erdosproblems.com/894](https://www.erdosproblems.com/894)
-/

namespace Erdos894

/--
A sequence $a : \mathbb{N} \to \mathbb{N}$ is lacunary if it is strictly increasing and there
exists some $\varepsilon > 0$ such that $a(k+1) \geq (1 + \varepsilon) \cdot a(k)$ for all $k$.
-/
def IsLacunary (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ ∃ ε : ℝ, ε > 0 ∧ ∀ k : ℕ, (a (k + 1) : ℝ) ≥ (1 + ε) * (a k : ℝ)

/--
Let $A = \{n_1 < n_2 < \cdots\} \subset \mathbb{N}$ be a lacunary sequence (there exists some
$\varepsilon > 0$ with $n_{k+1} \geq (1+\varepsilon) \cdot n_k$ for all $k$).

Is it true that there must exist a finite colouring of $\mathbb{N}$ with no monochromatic
solutions to $a - b \in A$?

Equivalently, does the Cayley graph on $\mathbb{Z}$ defined by a lacunary set have finite
chromatic number?

This was proved: the answer is yes. Katznelson [Ka01] observed it follows from the
solution to Problem 464 (on the Littlewood conjecture). The best quantitative
bound, due to Peres and Schlag [PeSc10], gives at most
$\ll \varepsilon^{-1} \log(1/\varepsilon)$ colours.
-/
@[category research solved, AMS 5]
theorem erdos_894 : answer(True) ↔
    ∀ (a : ℕ → ℕ), IsLacunary a →
      ∃ (k : ℕ) (c : ℕ → Fin k),
        ∀ x y : ℕ, x > y → (∃ i, a i = x - y) → c x ≠ c y := by
  sorry

end Erdos894
