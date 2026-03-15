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
import FormalConjecturesForMathlib.NumberTheory.AdditivelyComplete

/-!
# Erdős Problem 344

*Reference:* [erdosproblems.com/344](https://www.erdosproblems.com/344)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathématique (1980).

[SzVu06] Szemerédi, E. and Vu, V.H., *Finite and infinite arithmetic progressions in sumsets*.
Annals of Mathematics (2006).

[Er61b] Erdős, P., *On the representation of large integers as sums of distinct summands taken
from a fixed set*. Acta Arithmetica (1961/62), 345-354.
-/

open Classical

namespace Erdos344

/-- A set of natural numbers contains an infinite arithmetic progression:
there exist $a \geq 0$ and $d > 0$ such that $a + nd \in S$ for all $n \in \mathbb{N}$. -/
def ContainsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ (a d : ℕ), 0 < d ∧ ∀ n : ℕ, a + n * d ∈ S

/--
Erdős Problem 344 [ErGr80, p.54]:

If $A \subseteq \mathbb{N}$ is a set of positive integers such that
$|A \cap \{1,\ldots,N\}| \gg N^{1/2}$ (i.e., there exists $c > 0$ and $N_0$ such that
$|A \cap \{1,\ldots,N\}| \geq c\sqrt{N}$ for all $N \geq N_0$), then $A$ is subcomplete: the set
$P(A)$ of all finite subset sums of $A$ contains an infinite arithmetic progression.

This was proved by Szemerédi and Vu [SzVu06]. Folkman had previously proved this under the
stronger assumption $|A \cap \{1,\ldots,N\}| \geq cN^{1/2+\varepsilon}$ for some
$\varepsilon > 0$.
-/
@[category research solved, AMS 5 11]
theorem erdos_344
    (A : Set ℕ)
    (hA_pos : ∀ a ∈ A, 0 < a)
    (c : ℝ) (hc : 0 < c)
    (hgrowth : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * Real.sqrt (N : ℝ) ≤ (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) :
    ContainsInfiniteAP (subsetSums A) := by
  sorry

/--
Erdős Problem 344, sharp variant [Er61b]:

The stronger conjecture that the subset sums of $A$ contain an infinite arithmetic progression
under the condition $|A \cap \{1,\ldots,N\}| \geq (2N)^{1/2}$ for all $N$. This would be best
possible, as shown by Erdős [Er61b]. This variant remains open.
-/
@[category research open, AMS 5 11]
theorem erdos_344_sharp
    (A : Set ℕ)
    (hA_pos : ∀ a ∈ A, 0 < a)
    (hgrowth : ∀ N : ℕ, Real.sqrt (2 * N : ℝ) ≤
      (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) :
    ContainsInfiniteAP (subsetSums A) := by
  sorry

end Erdos344
