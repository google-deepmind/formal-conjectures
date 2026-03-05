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
# Erdős Problem 785

*Reference:* [erdosproblems.com/785](https://www.erdosproblems.com/785)

Let $A, B \subseteq \mathbb{N}$ be infinite sets such that $A + B$ contains all large integers.
Let $A(x) = |A \cap [1, x]|$ and similarly for $B(x)$. Is it true that if
$A(x)B(x) \sim x$ then $A(x)B(x) - x \to \infty$ as $x \to \infty$?

Such sets $A$ and $B$ (with all large integers in $A + B$ and $A(x)B(x) \sim x$) are
called exact additive complements. Danzer proved that exact additive complements exist.

The answer is yes, proved by Sárközy and Szemerédi [SaSz94].
Ruzsa [Ru17] has constructed, for any function $w(x) \to \infty$, such a pair
of sets with $A(x)B(x) - x < w(x)$ for infinitely many $x$.

[SaSz94] Sárközy, A. and Szemerédi, E.

[Ru17] Ruzsa, I. Z.
-/

open scoped Classical
open Filter

namespace Erdos785

/-- Counting function: $|A \cap \{1, \ldots, x\}|$ -/
noncomputable def countingFn (A : Set ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (· ∈ A)).card

/--
**Erdős Problem 785** (Sárközy and Szemerédi [SaSz94]):

Let $A, B \subseteq \mathbb{N}$ be infinite sets such that $A + B$ contains all sufficiently
large integers (i.e., $A$ and $B$ are additive complements). If $A(x)B(x) \sim x$
(exact additive complements), then $A(x)B(x) - x \to \infty$ as $x \to \infty$.
-/
@[category research solved, AMS 5 11]
theorem erdos_785 : answer(True) ↔
    ∀ (A B : Set ℕ), Set.Infinite A → Set.Infinite B →
    (∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → ∃ a ∈ A, ∃ b ∈ B, a + b = n) →
    Tendsto (fun x : ℕ => (countingFn A x * countingFn B x : ℝ) / (x : ℝ))
      atTop (nhds 1) →
    Tendsto (fun x : ℕ => (countingFn A x * countingFn B x : ℝ) - (x : ℝ))
      atTop atTop := by
  sorry

end Erdos785
