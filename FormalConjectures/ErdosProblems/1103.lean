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
# Erdős Problem 1103

*Reference:* [erdosproblems.com/1103](https://www.erdosproblems.com/1103)

Let $A = \{a_0 < a_1 < a_2 < \cdots\}$ be an infinite sequence of positive integers such that
every element of the sumset $A + A$ is squarefree. How fast must $A$ grow?

Erdős notes there exists such a sequence which grows exponentially, but does not
expect such a sequence of polynomial growth to exist.

van Doorn and Tao [vDTa25] showed $a_j > 0.24\, j^{4/3}$ for all $j$, and that there
exists such a sequence with $a_j < \exp(5j / \log j)$ for all large $j$.

[Er81h] Erdős, P., _Some applications of graph theory and combinatorial methods to number theory
and geometry_ (1981).

[vDTa25] van Doorn, F. and Tao, T., _Sumsets of squarefree numbers_ (2025).
-/

namespace Erdos1103

/--
Erdős Problem 1103 [Er81h, p.180]:

For any strictly increasing sequence $a : \mathbb{N} \to \mathbb{N}$ such that $a(i) + a(j)$ is
squarefree for all $i, j$, the sequence must grow super-polynomially: for every $C > 0$, we have
$a(j) > j^C$ for all sufficiently large $j$.
-/
@[category research open, AMS 11]
theorem erdos_1103
    (a : ℕ → ℕ)
    (ha_strict_mono : StrictMono a)
    (ha_sumset_sqfree : ∀ i j : ℕ, Squarefree (a i + a j)) :
    ∀ C : ℝ, C > 0 →
      ∃ N : ℕ, ∀ j : ℕ, j ≥ N →
        (j : ℝ) ^ C < (a j : ℝ) := by
  sorry

end Erdos1103
