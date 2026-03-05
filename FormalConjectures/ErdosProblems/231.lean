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
# Erdős Problem 231

*Reference:* [erdosproblems.com/231](https://www.erdosproblems.com/231)

Let $S$ be a string of length $2^k - 1$ formed from an alphabet of $k$ characters.
Must $S$ contain an abelian square: two consecutive blocks $x$ and $y$ such that
$y$ is a permutation of $x$?

Erdős initially conjectured the answer is yes for all $k \ge 2$, but this was
disproved for $k \ge 4$. Keränen [Ke92] constructed an infinite word over
$\{1,2,3,4\}$ with no abelian square, giving a negative answer for all $k \ge 4$.

The answer is:
- Yes for $k \le 3$ (any word of length $\ge 7$ over $3$ letters contains an
  abelian square)
- No for $k \ge 4$

[Ke92] Keränen, V., _Abelian squares are avoidable on 4 letters_. Automata, Languages
and Programming (1992), 41-52.
-/

namespace Erdos231

/-- A list contains an abelian square if there exist two consecutive blocks of
equal positive length that are permutations of each other. -/
def ContainsAbelianSquare {α : Type*} (w : List α) : Prop :=
  ∃ i n : ℕ, 0 < n ∧ i + 2 * n ≤ w.length ∧
    List.Perm ((w.drop i).take n) ((w.drop (i + n)).take n)

/--
Must every string of length $2^k - 1$ over an alphabet of $k \ge 2$ characters
contain an abelian square? The answer is no, disproved by Keränen [Ke92] for
$k \ge 4$.
-/
@[category research solved, AMS 5]
theorem erdos_231 : answer(False) ↔
    ∀ k, 2 ≤ k → ∀ w : List (Fin k), w.length = 2 ^ k - 1 →
      ContainsAbelianSquare w := by
  sorry

/--
For $k \le 3$ (with $k \ge 2$), every string of length $2^k - 1$ over $k$
characters contains an abelian square.
-/
@[category research solved, AMS 5]
theorem erdos_231.variants.small_alphabet (k : ℕ) (hk : 2 ≤ k) (hk3 : k ≤ 3)
    (w : List (Fin k)) (hw : w.length = 2 ^ k - 1) :
    ContainsAbelianSquare w := by
  sorry

/--
For $k \ge 4$, there exists a string of length $2^k - 1$ over $k$ characters with
no abelian square, disproving the original conjecture. See [Ke92].
-/
@[category research solved, AMS 5]
theorem erdos_231.variants.large_alphabet (k : ℕ) (hk : 4 ≤ k) :
    ∃ w : List (Fin k), w.length = 2 ^ k - 1 ∧ ¬ContainsAbelianSquare w := by
  sorry

end Erdos231
