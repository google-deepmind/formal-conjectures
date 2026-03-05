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
# Erdős Problem 192

*Reference:* [erdosproblems.com/192](https://www.erdosproblems.com/192)

Let $A = \{a_1, a_2, \ldots\} \subset \mathbb{R}^d$ be an infinite sequence such that
$a_{i+1} - a_i$ is a positive unit vector (i.e. of the form $(0,\ldots,1,\ldots,0)$). For which
$d$ must $A$ contain a three-term arithmetic progression?

This is equivalent to the following question about abelian squares: for which $d$ does every
infinite word over a $d$-letter alphabet contain an abelian square (a pair of consecutive blocks
that are permutations of each other)?

The answer is: true for $d \le 3$, false for $d \ge 4$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[Ke92] Keränen, V., *Abelian squares are avoidable on 4 letters*. Automata, languages and
programming (Vienna, 1992), Lecture Notes in Comput. Sci. 623, Springer (1992), 41–52.
-/

namespace Erdos192

/-- An infinite word $w : \mathbb{N} \to \alpha$ contains an abelian square if there exist
a starting position $i$ and a block length $n \ge 1$ such that the multiset
of characters in positions $i, \ldots, i+n-1$ equals the multiset of characters
in positions $i+n, \ldots, i+2n-1$. -/
def HasAbelianSquare {α : Type*} (w : ℕ → α) : Prop :=
  ∃ i n : ℕ, 0 < n ∧
    (Finset.range n).val.map (fun j => w (i + j)) =
    (Finset.range n).val.map (fun j => w (i + n + j))

/--
Erdős Problem 192, Part 1 [ErGr80]:
Every infinite word over a 3-letter alphabet contains an abelian square.
Equivalently, any infinite sequence in $\mathbb{R}^3$ with unit-vector steps must
contain a three-term arithmetic progression.

In fact, any finite word of length $\ge 7$ over $\{0,1,2\}$ contains an abelian square.
-/
@[category research solved, AMS 5]
theorem erdos_192 :
    ∀ w : ℕ → Fin 3, HasAbelianSquare w := by
  sorry

/--
Erdős Problem 192, Part 2 [ErGr80]:
There exists an infinite word over a 4-letter alphabet with no abelian square.
Equivalently, there exists an infinite sequence in $\mathbb{R}^4$ with unit-vector steps
that contains no three-term arithmetic progression.

Proved by Keränen [Ke92].
-/
@[category research solved, AMS 5]
theorem erdos_192.variants.four_letters :
    ∃ w : ℕ → Fin 4, ¬HasAbelianSquare w := by
  sorry

end Erdos192
