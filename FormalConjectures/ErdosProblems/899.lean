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
# Erdős Problem 899

*Reference:* [erdosproblems.com/899](https://www.erdosproblems.com/899)
-/

open Filter

open scoped Pointwise Topology

namespace Erdos899

open Erdos899

/--
Let $A\subseteq\mathbb{N}$ be an infinite set such that $|A\cap \{1, ..., N\}| = o(N)$.
Is it true that
$$
\limsup_{N\to\infty}\frac{|(A - A)\cap \{1, ..., N\}|}{|A \cap \{1, ..., N\}|} = \infty?
$$

The answer is yes, proved by Ruzsa [Ru78].

[Ru78] Ruzsa, I. Z., _On the cardinality of {$A+A$}\ and {$A-A$}_. (1978), 933--938.
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/899.lean", AMS 5]
theorem erdos_899 : answer(True) ↔ ∀ (A : Set ℕ), A.Infinite →
    Tendsto (fun N => (A.interIcc 1 N |>.ncard : ℝ) / N) atTop (𝓝 0) →
    atTop.limsup (fun N => ((A - A : Set ℕ).interIcc 1 N |>.ncard : EReal) /
      (A.interIcc 1 N).ncard) = ⊤ := by
  sorry

end Erdos899

