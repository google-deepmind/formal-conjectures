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
# Erdős Problem 190

*Reference:* [erdosproblems.com/190](https://www.erdosproblems.com/190)

Let $H(k)$ be the smallest $N$ such that in any finite colouring of $\{1,\ldots,N\}$
(into any number of colours) there is always either a monochromatic $k$-term
arithmetic progression or a rainbow arithmetic progression (i.e. all
elements are different colours). Estimate $H(k)$. Is it true that
$H(k)^{1/k}/k \to \infty$ as $k \to \infty$?

This type of problem belongs to 'canonical' Ramsey theory. The existence
of $H(k)$ follows from Szemerédi's theorem, and it is easy to show that
$H(k)^{1/k} \to \infty$.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathématique (1980).
-/

open Filter Real

namespace Erdos190

/-- A colouring $\chi : \mathbb{N} \to \mathbb{N}$ has a monochromatic $k$-term arithmetic
progression within $\{1,\ldots,N\}$: there exist $a \geq 1$ and $d \geq 1$ such that
$a, a+d, \ldots, a+(k-1) \cdot d$ are all in $\{1,\ldots,N\}$ and all share the same colour. -/
def HasMonoAP (χ : ℕ → ℕ) (N k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (k - 1) * d ≤ N ∧
    ∀ i : ℕ, i < k → χ (a + i * d) = χ a

/-- A colouring $\chi : \mathbb{N} \to \mathbb{N}$ has a rainbow $3$-term arithmetic
progression within $\{1,\ldots,N\}$: there exist $a \geq 1$ and $d \geq 1$ such that
$a, a+d, a+2d$ are all in $\{1,\ldots,N\}$ and their colours are pairwise distinct. -/
def HasRainbowAP (χ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + 2 * d ≤ N ∧
    χ a ≠ χ (a + d) ∧ χ a ≠ χ (a + 2 * d) ∧ χ (a + d) ≠ χ (a + 2 * d)

/-- $H(k)$ is the smallest $N$ such that any colouring of $\{1,\ldots,N\}$ contains
either a monochromatic $k$-term AP or a rainbow $3$-term AP. -/
noncomputable def H (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ χ : ℕ → ℕ, HasMonoAP χ N k ∨ HasRainbowAP χ N}

/--
Erdős Problem 190 [ErGr80]:

Is it true that $H(k)^{1/k}/k \to \infty$ as $k \to \infty$, where $H(k)$ is the smallest $N$
such that any finite colouring of $\{1,\ldots,N\}$ always contains either a monochromatic
$k$-term arithmetic progression or a rainbow arithmetic progression?
-/
@[category research open, AMS 5]
theorem erdos_190 : answer(sorry) ↔
    Tendsto (fun k : ℕ => (H k : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / (k : ℝ)) atTop atTop := by
  sorry

end Erdos190
