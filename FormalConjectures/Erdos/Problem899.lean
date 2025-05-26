/-
Copyright 2025 Google LLC

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
# Erdős Problem 899

*Reference:* [erdosproblems.com/899](https://www.erdosproblems.com/899)
-/
open Filter

open scoped Pointwise Topology

/-- If `A` is a set of natural numbers and `N : ℕ`, then `bdd A N` is the
set `{ n ∈ A | 1 ≤ n ≤ N }`. -/
def Set.bdd (A : Set ℕ) (N : ℕ) := A ∩ Set.Icc 1 N

/--
Let $A\subseteq\mathbb{N}$ be an infinite set such that $|A\cap \{1, ..., N\}| = o(N)$.
Is it true that
$$
\limsup_{N\to\infty}\frac{|(A - A)\cap \{1, ..., N\}|}{|A \cap \{1, ..., N\}|} = \infty?
$$
-/
@[category research solved, AMS 5]
theorem erdos_899 (A : Set ℕ) (h_inf : A.Infinite)
    (hf : Tendsto (fun N => (A.bdd N |>.ncard : ℝ) / N) atTop (𝓝 0)) :
    Tendsto (fun N => ((A - A : Set ℕ).bdd N |>.ncard : ℝ) / (A.bdd N).ncard) atTop atTop :=
  sorry
