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
# Erdős Problem 297

*Reference:* [erdosproblems.com/297](https://www.erdosproblems.com/297)

Let $N \geq 1$. How many $A \subseteq \{1, \ldots, N\}$ are there such that
$\sum_{n \in A} \frac{1}{n} = 1$?

It was not even known for a long time whether this is $2^{cN}$ for some $c < 1$ or
$2^{(1+o(1))N}$. In fact the former is true, and the correct value of $c$ is now known.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[St24] Steinerberger, S., proved the count is at most $2^{0.93N}$.

[LiSa24] Liu, H. and Sawhney, M., gave both upper and lower bounds, proving that the
count is $2^{(0.91\ldots+o(1))N}$.

[CFHMPSV24] Conlon, D., Fox, J., He, X., Mubayi, D., Pham, H.T., Suk, A., and Verstraëte, J.
-/

open Filter

open scoped Topology

namespace Erdos297

/-- Count of subsets $A \subseteq \{1, \ldots, N\}$ such that
$\sum_{n \in A} \frac{1}{n} = 1$. -/
noncomputable def unitFractionSubsetCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter fun (A : Finset ℕ) =>
    (A.sum fun n => (1 : ℚ) / (n : ℚ)) = 1).card

/--
Erdős Problem 297 [ErGr80, p.36]

There exists a constant $c \in (0, 1)$ such that the number of subsets
$A \subseteq \{1, \ldots, N\}$ with $\sum_{n \in A} \frac{1}{n} = 1$ is $2^{(c+o(1))N}$.

Equivalently, $\log_2(\mathrm{count}(N)) / N \to c$ as $N \to \infty$.

Steinerberger [St24] proved the count is at most $2^{0.93N}$. Independently,
Liu and Sawhney [LiSa24] gave both upper and lower bounds, proving that the
count is $2^{(0.91\ldots+o(1))N}$, where $0.91\ldots$ is an explicit number defined as
the solution to a certain integral equation. Again independently, the same
asymptotic was proved by Conlon–Fox–He–Mubayi–Pham–Suk–Verstraëte [CFHMPSV24].
-/
@[category research solved, AMS 5 11]
theorem erdos_297 :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      Tendsto (fun N : ℕ =>
        Real.log (unitFractionSubsetCount N : ℝ) / (Real.log 2 * (N : ℝ)))
        atTop (nhds c) := by
  sorry

end Erdos297
