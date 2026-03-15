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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 374

*Reference:* [erdosproblems.com/374](https://www.erdosproblems.com/374)

For a natural number $m$, let $F(m)$ be the minimal $k \ge 2$ such that there exist
$a_1 < \cdots < a_k = m$ with $a_1! \cdots a_k!$ a perfect square, and let $D_k = \{m : F(m) = k\}$.
The conjecture asserts that $D_6$ has positive lower density, i.e., $|D_6 \cap \{1,\ldots,n\}| \gg n$.

[ErGr76] Erdős, P. and Graham, R., _On products of factorials_. Bull. Inst. Math. Acad. Sinica
(1976), 337-355.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).

[LSS14] Luca, F., Saradha, N., and Shorey, T. N., _Squares and factorials in products of
factorials_. Monatshefte für Mathematik (2014), 385-400.
-/

open scoped BigOperators
open Filter Classical

namespace Erdos374

/--
There exists a set of $k$ distinct natural numbers with maximum element $m$
whose product of factorials is a perfect square.
Formally: there exist $a_1 < \cdots < a_k = m$ with $a_1! \cdots a_k!$ a square.
-/
def HasFactorialSquareSeq (m : ℕ) (k : ℕ) : Prop :=
  ∃ (s : Finset ℕ), s.card = k ∧ k ≥ 2 ∧ m ∈ s ∧
    (∀ x ∈ s, x ≤ m) ∧
    IsSquare (∏ x ∈ s, Nat.factorial x)

/--
$m \in D_k$: the minimal factorial-square sequence length for $m$ is exactly $k$.
$F(m) = k$ where $F(m)$ is the minimal $k \ge 2$ such that there exist
$a_1 < \cdots < a_k = m$ with $a_1! \cdots a_k!$ a perfect square.
-/
def IsInD (k : ℕ) (m : ℕ) : Prop :=
  HasFactorialSquareSeq m k ∧ ∀ j, j < k → ¬HasFactorialSquareSeq m j

/--
Erdős Problem 374 [ErGr76][ErGr80][LSS14]:

For $m \in \mathbb{N}$, let $F(m)$ be the minimal $k \ge 2$ such that there exist
$a_1 < \cdots < a_k = m$ with $a_1! \cdots a_k!$ a perfect square.
Let $D_k = \{m : F(m) = k\}$.

Conjecture: $|D_6 \cap \{1, \ldots, n\}| \gg n$, i.e., $D_6$ has positive lower density.
-/
@[category research open, AMS 11]
theorem erdos_374 :
    0 < Set.lowerDensity {m : ℕ | IsInD 6 m} := by
  sorry

end Erdos374
