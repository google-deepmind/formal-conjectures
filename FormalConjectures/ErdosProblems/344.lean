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
# Erdős Problem 344

*Reference:* [erdosproblems.com/344](https://www.erdosproblems.com/344)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathématique (1980).

[SzVu06] Szemerédi, E. and Vu, V.H., *Finite and infinite arithmetic progressions in sumsets*.
Annals of Mathematics (2006).
-/

open Classical

namespace Erdos344

/-- The subset sum set $P(A)$: the set of all sums $\sum_{n \in B} n$ for finite
$B \subseteq A$. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {s : ℕ | ∃ (B : Finset ℕ), (↑B : Set ℕ) ⊆ A ∧ B.sum id = s}

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

end Erdos344
