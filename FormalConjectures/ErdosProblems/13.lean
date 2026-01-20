/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 13

*Reference:* [erdosproblems.com/13](https://www.erdosproblems.com/13)
-/

open Finset
open Nat

namespace Erdos13

/--
A finite set of naturals `A` is said to be forbidden-triple-free if for all `a, b, c ∈ A`,
if `a < min(b, c)` then `a` does not divide `b + c`.
-/
def IsForbiddenTripleFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < min b c → ¬ (a ∣ b + c)

/--
If $A \subseteq \{1, ..., N\}$ is a set with no $a, b, c \in A$ such that $a | (b+c)$ and
$a < \min(b,c)$, then $|A| \le N/3 + O(1)$. This has been solved by Bedert [Be23].

[Be23] Bedert, B., _On a problem of Erdős and Sárközy about sequences with no term dividing
the sum of two larger terms_. arXiv:2301.07065 (2023).
-/
@[category research solved, AMS 5 11]
theorem erdos_13 : ∃ C : ℝ, ∀ N : ℕ, ∀ A ⊆ Icc 1 N, IsForbiddenTripleFree A →
    (A.card : ℝ) ≤ (N : ℝ) / 3 + C := by
  sorry

/--
A general version asks, for a fixed $r \in \mathbb{N}$, if a set
$A \subseteq \{1, ..., N\}$ has no $a \in A$ and $b_1, ..., b_r \in A$ such that
$a | (b_1 + ... + b_r)$ and $a < \min(b_1, ..., b_r)$, then is it true that
$|A| \le N/(r+1) + O(1)$?
-/
@[category research open, AMS 5 11]
theorem erdos_13_general (r : ℕ) : ∃ C : ℝ, ∀ N : ℕ,
    ∀ A ⊆ Icc 1 N,
    (∀ a ∈ A, ∀ (b : Fin r → ℕ), (∀ i, b i ∈ A) → (∀ i, a < b i) →
      ¬ (a ∣ ∑ i, b i)) →
    (A.card : ℝ) ≤ (N : ℝ) / (r + 1) + C := by
  sorry

end Erdos13
